import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Homotopy.LocallyContractible
import JJMath.Topology.SheafAcyclicResolution

/-!
# Singular cohomology

This file defines singular cohomology with coefficients in a commutative ring
as the cohomology of the cochain complex obtained from the singular chain
complex by applying the linear Yoneda functor.

The main formal point needed later is contravariance: a continuous map
`X ⟶ Y` induces a map on cohomology from `Y` to `X`.  The categorical
retraction argument is proved here.
-/

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open Opposite
open TopologicalSpace
open scoped Topology

namespace JJMath
namespace Cohomology

noncomputable section

universe u v

/--
%%handwave
name:
  Coefficients for singular cohomology
statement:
  The coefficient module for singular cohomology is the ground ring, regarded
  as a module in the universe of the singular chains.
proof:
  Use the universe-lift functor for module categories.  This changes only the
  formal universe of the coefficient module, not its mathematical content.
-/
abbrev SingularCohomologyCoefficient (R : Type u) [CommRing R] :
    ModuleCat.{max u v} R :=
  (ModuleCat.uliftFunctor.{v, u} R).obj (ModuleCat.of R R)

/--
%%handwave
name:
  Singular chains with coefficients
statement:
  The singular chain complex of a space with coefficients in a commutative
  ring is the usual singular chain complex with the coefficient module in each
  simplex.
proof:
  Apply Mathlib's singular chain complex functor to the lifted coefficient
  module.
-/
abbrev SingularChains (R : Type u) [CommRing R] (X : TopCat.{v}) :
    ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max u v} R)).obj
    (SingularCohomologyCoefficient.{u, v} R)).obj X

/--
%%handwave
name:
  Singular homology
statement:
  Singular homology in degree \(n\) is the \(n\)-th homology object of the
  singular chain complex.
proof:
  This is the homology object of the chain complex in degree \(n\).
-/
abbrev SingularHomology (R : Type u) [CommRing R] (X : TopCat.{v}) (n : ℕ) :
    ModuleCat.{max u v} R :=
  (SingularChains R X).homology n

/-- Real singular homology. -/
abbrev RealSingularHomology (X : TopCat.{v}) (n : ℕ) :
    ModuleCat.{v} ℝ :=
  SingularHomology ℝ X n

/--
%%handwave
name:
  Singular cochain complex
statement:
  The singular cochain complex of a space is obtained from singular chains by
  taking linear maps from chains to the coefficient module.
proof:
  Apply the linear Yoneda construction to the singular chain complex.
-/
abbrev SingularCochainComplex (R : Type u) [CommRing R] (X : TopCat.{v}) :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  (SingularChains R X).linearYonedaObj R
    (SingularCohomologyCoefficient.{u, v} R)

/--
%%handwave
name:
  Singular cohomology
statement:
  Singular cohomology in degree \(n\) is the \(n\)-th cohomology object of the
  singular cochain complex.
proof:
  This is the homology object of the cochain complex in degree \(n\).
-/
abbrev SingularCohomology (R : Type u) [CommRing R] (X : TopCat.{v}) (n : ℕ) :
    ModuleCat.{max u v} R :=
  (SingularCochainComplex R X).homology n

/-- Real singular cohomology. -/
abbrev RealSingularCohomology (X : TopCat.{v}) (n : ℕ) :
    ModuleCat.{v} ℝ :=
  SingularCohomology ℝ X n

/--
%%handwave
name:
  Pullback on singular cochains
statement:
  A continuous map \(f:X\to Y\) induces a cochain map
  \(C^\bullet(Y;R)\to C^\bullet(X;R)\).
proof:
  First push singular chains forward along \(f\), then precompose linear
  cochains with that chain map.  The opposite-complex equivalence converts the
  resulting map into a cochain map in the ordinary direction.
-/
abbrev singularCochainMap (R : Type u) [CommRing R] {X Y : TopCat.{v}} (f : X ⟶ Y) :
    SingularCochainComplex R Y ⟶ SingularCochainComplex R X :=
  (HomologicalComplex.unopFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op
      ((((linearYoneda R (ModuleCat.{max u v} R)).obj
            (SingularCohomologyCoefficient.{u, v} R)).rightOp.mapHomologicalComplex _).map
        (((AlgebraicTopology.singularChainComplexFunctor
              (ModuleCat.{max u v} R)).obj
            (SingularCohomologyCoefficient.{u, v} R)).map f)))

/--
%%handwave
name:
  Identity pullback on cochains
statement:
  Pulling singular cochains back along the identity map is the identity
  cochain map.
proof:
  Expand the construction and use functoriality of singular chains, linear
  Yoneda, opposites, and the opposite-complex functor.
-/
theorem singularCochainMap_id (R : Type u) [CommRing R] (X : TopCat.{v}) :
    singularCochainMap R (𝟙 X) = 𝟙 (SingularCochainComplex R X) := by
  unfold singularCochainMap SingularCochainComplex SingularChains
    ChainComplex.linearYonedaObj
  rw [CategoryTheory.Functor.map_id]
  rw [CategoryTheory.Functor.map_id]
  rw [CategoryTheory.op_id]
  rw [CategoryTheory.Functor.map_id]
  rfl

/--
%%handwave
name:
  Composition of pullbacks on cochains
statement:
  Pullback of singular cochains reverses composition:
  \((g\circ f)^*=f^*\circ g^*\).
proof:
  Expand the construction and use functoriality together with the rule that
  taking opposites reverses composition.
-/
theorem singularCochainMap_comp (R : Type u) [CommRing R] {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    singularCochainMap R (f ≫ g) =
      singularCochainMap R g ≫ singularCochainMap R f := by
  unfold singularCochainMap SingularCochainComplex SingularChains
    ChainComplex.linearYonedaObj
  rw [CategoryTheory.Functor.map_comp]
  rw [CategoryTheory.Functor.map_comp]
  rw [CategoryTheory.op_comp]
  rw [CategoryTheory.Functor.map_comp]
  rfl

/--
%%handwave
name:
  Singular cochains as a contravariant functor
statement:
  Singular cochains form a contravariant functor from spaces to cochain
  complexes.
proof:
  Use pullback of cochains on morphisms.  The identity and composition laws
  are the identity and composition laws for singular-cochain pullback.
-/
@[simps! obj map]
abbrev singularCochainComplexFunctor (R : Type u) [CommRing R] :
    TopCat.{v}ᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ where
  obj X := SingularCochainComplex R (unop X)
  map f := singularCochainMap R f.unop
  map_id X := by
    simpa using singularCochainMap_id R (unop X)
  map_comp f g := by
    simpa using singularCochainMap_comp R g.unop f.unop

/--
%%handwave
name:
  Real singular cochains as a module-valued functor
statement:
  Real singular cochains form a contravariant functor from spaces to cochain
  complexes of real vector spaces.
proof:
  Specialize the singular-cochain functor to real coefficients.
-/
abbrev realSingularCochainModuleComplexFunctor :
    TopCat.{v}ᵒᵖ ⥤ CochainComplex (ModuleCat.{v} ℝ) ℕ :=
  singularCochainComplexFunctor (R := ℝ)

/--
%%handwave
name:
  Real singular cochains as additive-group complexes
statement:
  Real singular cochains form a contravariant functor from spaces to cochain
  complexes of abelian groups.
proof:
  Forget the real vector-space structure in the functor of real singular
  cochain complexes.
-/
abbrev realSingularCochainComplexAddFunctor :
    TopCat.{v}ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
  realSingularCochainModuleComplexFunctor ⋙
    (forget₂ (ModuleCat.{v} ℝ) AddCommGrpCat.{v}).mapHomologicalComplex
      (ComplexShape.up ℕ)

/--
%%handwave
name:
  Real singular cochains on open subsets as vector-space complexes
statement:
  The open subsets of a space carry the cochain-complex-valued presheaf
  \(U\mapsto C^\bullet(U;\mathbb R)\) before forgetting the real vector-space
  structure.
proof:
  Send an open subset to its associated topological space and apply the
  contravariant functor of real singular cochains.
-/
abbrev realSingularCochainOpenModuleComplexFunctor (X : TopCat.{v}) :
    (Opens X)ᵒᵖ ⥤ CochainComplex (ModuleCat.{v} ℝ) ℕ :=
  (Opens.toTopCat X).op ⋙ realSingularCochainModuleComplexFunctor

/--
%%handwave
name:
  Real singular cochains on open subsets
statement:
  The open subsets of a space carry the presheaf-valued cochain complex
  \(U\mapsto C^\bullet(U;\mathbb R)\).
proof:
  Send an open subset to its associated topological space and apply the
  contravariant functor of real singular cochains.
-/
abbrev realSingularCochainOpenComplexFunctor (X : TopCat.{v}) :
    (Opens X)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
  realSingularCochainOpenModuleComplexFunctor X ⋙
    (forget₂ (ModuleCat.{v} ℝ) AddCommGrpCat.{v}).mapHomologicalComplex
      (ComplexShape.up ℕ)

/--
%%handwave
name:
  Scalar multiplication on open singular cochains
statement:
  Multiplication by a real scalar is a natural cochain endomorphism of
  \(U\mapsto C^\bullet(U;\mathbb R)\) after forgetting to abelian groups.
proof:
  Use the natural scalar-multiplication endomorphism of the forgetful functor
  from real vector spaces to abelian groups, and apply it degreewise to
  cochain complexes.
-/
def realSingularCochainOpenComplexFunctorScalarNatTrans (X : TopCat.{v}) (r : ℝ) :
    realSingularCochainOpenComplexFunctor X ⟶
      realSingularCochainOpenComplexFunctor X :=
  Functor.whiskerLeft (realSingularCochainOpenModuleComplexFunctor X)
    (NatTrans.mapHomologicalComplex
      ((ModuleCat.smulNatTrans ℝ) r) (ComplexShape.up ℕ))

/--
%%handwave
name:
  The open singular-cochain presheaf complex
statement:
  The assignment \(U\mapsto C^\bullet(U;\mathbb R)\) is a cochain complex of
  abelian-group presheaves on \(X\).
proof:
  In degree \(p\), take the presheaf \(U\mapsto C^p(U;\mathbb R)\).  The
  coboundary maps are natural because restriction of cochains is a cochain
  map.
-/
def realSingularCochainOpenPresheafComplex (X : TopCat.{v}) :
    CochainComplex (TopCat.Presheaf AddCommGrpCat.{v} X) ℕ where
  X n :=
    { obj := fun U => ((realSingularCochainOpenComplexFunctor X).obj U).X n
      map := fun f => ((realSingularCochainOpenComplexFunctor X).map f).f n
      map_id := by
        intro U
        simpa using
          congrArg (fun φ => φ.f n)
            ((realSingularCochainOpenComplexFunctor X).map_id U)
      map_comp := by
        intro U V W f g
        simpa using
          congrArg (fun φ => φ.f n)
            ((realSingularCochainOpenComplexFunctor X).map_comp f g) }
  d n m :=
    { app := fun U => ((realSingularCochainOpenComplexFunctor X).obj U).d n m
      naturality := by
        intro U V f
        exact ((realSingularCochainOpenComplexFunctor X).map f).comm n m }
  shape n m hnm := by
    ext U x
    simpa using
      congrArg
        (fun f =>
          (AddCommGrpCat.Hom.hom f) x)
        (((realSingularCochainOpenComplexFunctor X).obj (op U)).shape n m hnm)
  d_comp_d' n m k hnm hmk := by
    ext U x
    simpa using
      congrArg
        (fun f =>
          (AddCommGrpCat.Hom.hom f) x)
        (((realSingularCochainOpenComplexFunctor X).obj (op U)).d_comp_d' n m k hnm hmk)

/--
%%handwave
name:
  Scalar multiplication on the open singular-cochain presheaf complex
statement:
  Multiplication by a real scalar gives a cochain endomorphism of the
  presheaf complex \(U\mapsto C^\bullet(U;\mathbb R)\).
proof:
  Convert the scalar natural endomorphism of the cochain-complex-valued
  presheaf into a morphism of the corresponding cochain complex of
  presheaves.
-/
def realSingularCochainOpenPresheafComplexScalarEnd
    (X : TopCat.{v}) (r : ℝ) :
    realSingularCochainOpenPresheafComplex X ⟶
      realSingularCochainOpenPresheafComplex X where
  f n :=
    { app := fun U =>
        ((realSingularCochainOpenComplexFunctorScalarNatTrans X r).app U).f n
      naturality := by
        intro U V f
        simpa using
          congrArg (fun φ => φ.f n)
            ((realSingularCochainOpenComplexFunctorScalarNatTrans X r).naturality f) }
  comm' n m hnm := by
    ext U x
    simpa using
      congrArg
        (fun f =>
          (AddCommGrpCat.Hom.hom f) x)
        (((realSingularCochainOpenComplexFunctorScalarNatTrans X r).app (op U)).comm n m)

/--
%%handwave
name:
  The sheafified singular-cochain complex
statement:
  Sheafifying degreewise turns the presheaf complex
  \(U\mapsto C^\bullet(U;\mathbb R)\) into a cochain complex of sheaves.
proof:
  Apply the sheafification functor to the open singular-cochain presheaf
  complex.
-/
abbrev realSingularCochainSheafComplex (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    CochainComplex
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}) ℕ :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).mapHomologicalComplex
      (ComplexShape.up ℕ) |>.obj
    (realSingularCochainOpenPresheafComplex X)

/--
%%handwave
name:
  Scalar multiplication on the sheafified open singular-cochain complex
statement:
  Multiplication by a real scalar gives a cochain endomorphism of the
  sheafified open singular-cochain complex.
proof:
  Sheafify the scalar endomorphism of the open singular-cochain presheaf
  complex.
-/
def sheafifiedOpenRealSingularCochainSheafScalarEndConcrete
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (r : ℝ) :
    realSingularCochainSheafComplex X ⟶ realSingularCochainSheafComplex X :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      (realSingularCochainOpenPresheafComplexScalarEnd X r)

section ConstantSheaf

/--
%%handwave
name:
  Sheafification for abelian-group sheaves on a space
statement:
  The inclusion of abelian-group sheaves on the open-set site of a topological
  space has a left exact left adjoint.
proof:
  Use the standard plus-plus sheafification construction for concrete
  categories with finite limits, specialized to abelian groups.
tags:
  milestone
-/
theorem opens_addCommGrp_hasSheafify (X : TopCat.{v}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v} := by
  infer_instance

/--
%%handwave
name:
  Ext groups for abelian-group sheaves on a space
statement:
  The category of abelian-group sheaves on the open-set site of a topological
  space has the Ext groups used to define sheaf cohomology.
proof:
  Once sheafification is available, abelian-group sheaves form a Grothendieck
  abelian category, so derived Hom and Ext groups exist.
-/
theorem opens_addCommGrp_hasExt (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}) := by
  infer_instance

/--
%%handwave
name:
  The constant real abelian sheaf
statement:
  The real constant sheaf, viewed as an abelian-group-valued sheaf, is the
  sheafification of the constant presheaf with value \(\mathbb R\).
proof:
  Apply the constant-sheaf functor for abelian groups to the additive group of
  the universe-lifted real numbers.
-/
abbrev RealConstantAddSheaf (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v} :=
  (constantSheaf
      (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj
      (AddCommGrpCat.of (ULift.{v} ℝ))

/--
%%handwave
name:
  Real constant-sheaf cohomology
statement:
  Real constant-sheaf cohomology of a space is sheaf cohomology of the
  constant sheaf with value \(\mathbb R\).
proof:
  Apply Mathlib's sheaf cohomology construction to the constant abelian-group
  sheaf with value \(\mathbb R\).
-/
abbrev RealConstantSheafCohomology (X : TopCat.{v}) (n : ℕ)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] :
    Type v :=
  (RealConstantAddSheaf X).H n

noncomputable instance constantSheaf_addCommGrp_additive (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).Additive := by
  let F : AddCommGrpCat.{v} ⥤ (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v} :=
    Functor.const (TopologicalSpace.Opens X)ᵒᵖ
  change (F ⋙ presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).Additive
  haveI : F.Additive := by
    constructor
    intro A B f g
    ext U
    rfl
  infer_instance

/--
%%handwave
name:
  Scalar multiplication on the constant real group
statement:
  A real number \(r\) acts on the universe-lifted additive group
  \(\mathbb R\) by multiplication.
proof:
  This is the additive group homomorphism \(x\mapsto rx\).
-/
def realULiftScalarAddMonoidHom (r : ℝ) : ULift.{v} ℝ →+ ULift.{v} ℝ where
  toFun x := ULift.up (r * x.down)
  map_zero' := by
    ext
    simp
  map_add' x y := by
    ext
    simp [mul_add]

@[simp]
theorem realULiftScalarAddMonoidHom_apply (r : ℝ) (x : ULift.{v} ℝ) :
    realULiftScalarAddMonoidHom.{v} r x = ULift.up (r * x.down) :=
  rfl

@[simp]
theorem realULiftScalarAddMonoidHom_one :
    realULiftScalarAddMonoidHom.{v} (1 : ℝ) =
      AddMonoidHom.id (ULift.{v} ℝ) := by
  ext x
  cases x
  simp

theorem realULiftScalarAddMonoidHom_mul (r s : ℝ) :
    realULiftScalarAddMonoidHom.{v} (r * s) =
      (realULiftScalarAddMonoidHom.{v} r).comp
        (realULiftScalarAddMonoidHom.{v} s) := by
  ext x
  cases x
  simp [mul_assoc]

@[simp]
theorem realULiftScalarAddMonoidHom_zero :
    realULiftScalarAddMonoidHom.{v} (0 : ℝ) =
      0 := by
  ext x
  cases x
  simp

theorem realULiftScalarAddMonoidHom_add (r s : ℝ) :
    realULiftScalarAddMonoidHom.{v} (r + s) =
      realULiftScalarAddMonoidHom.{v} r +
        realULiftScalarAddMonoidHom.{v} s := by
  ext x
  cases x
  simp [add_mul]

/--
%%handwave
name:
  Scalar endomorphisms of the constant real sheaf
statement:
  Multiplication by a real number induces an endomorphism of the constant real
  abelian sheaf.
proof:
  Apply the constant-sheaf functor to the additive homomorphism
  \(x\mapsto rx\).
-/
noncomputable def realConstantSheafScalarEnd (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (r : ℝ) :
    RealConstantAddSheaf X ⟶ RealConstantAddSheaf X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).map
    (AddCommGrpCat.ofHom (realULiftScalarAddMonoidHom.{v} r))

@[simp]
theorem realConstantSheafScalarEnd_one (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    realConstantSheafScalarEnd X (1 : ℝ) = 𝟙 (RealConstantAddSheaf X) := by
  simp [realConstantSheafScalarEnd]

@[simp]
theorem realConstantSheafScalarEnd_zero (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    realConstantSheafScalarEnd X (0 : ℝ) = 0 := by
  rw [realConstantSheafScalarEnd, realULiftScalarAddMonoidHom_zero]
  exact Functor.map_zero _ _ _

theorem realConstantSheafScalarEnd_add (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (r s : ℝ) :
    realConstantSheafScalarEnd X (r + s) =
      realConstantSheafScalarEnd X r + realConstantSheafScalarEnd X s := by
  rw [realConstantSheafScalarEnd, realULiftScalarAddMonoidHom_add]
  exact Functor.map_add _

theorem realConstantSheafScalarEnd_mul (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (r s : ℝ) :
    realConstantSheafScalarEnd X (r * s) =
      realConstantSheafScalarEnd X s ≫ realConstantSheafScalarEnd X r := by
  simp [realConstantSheafScalarEnd, realULiftScalarAddMonoidHom_mul]

/--
%%handwave
name:
  The constant real presheaf on open subsets
statement:
  The constant real presheaf assigns the additive group \(\mathbb R\) to
  every open subset.
proof:
  This is the constant functor with value the universe-lifted additive group
  of real numbers.
-/
abbrev realConstantOpenPresheaf (X : TopCat.{v}) :
    TopCat.Presheaf AddCommGrpCat.{v} X :=
  (Functor.const (TopologicalSpace.Opens X)ᵒᵖ).obj
    (AddCommGrpCat.of (ULift.{v} ℝ))

/--
%%handwave
name:
  Scalar multiplication on the constant real presheaf
statement:
  Multiplication by a real scalar gives an endomorphism of the constant real
  presheaf on open subsets.
proof:
  Apply the constant-presheaf functor to scalar multiplication of the
  universe-lifted real additive group.
-/
def realConstantOpenPresheafScalarEnd (X : TopCat.{v}) (r : ℝ) :
    realConstantOpenPresheaf X ⟶ realConstantOpenPresheaf X :=
  (Functor.const (TopologicalSpace.Opens X)ᵒᵖ).map
    (AddCommGrpCat.ofHom (realULiftScalarAddMonoidHom.{v} r))

/--
%%handwave
name:
  A presheaf degree-zero augmented singular-cochain short complex from a chosen augmentation
statement:
  Any map from the constant real presheaf to singular zero-cochains which is
  killed by the first coboundary determines a degree-zero augmented short
  complex of presheaves.
proof:
  Use the given map as the augmentation and the first singular coboundary as
  the second map.
-/
abbrev realSingularCochainOpenPresheafAugmentationShortComplexOf
    (X : TopCat.{v})
    (η :
      realConstantOpenPresheaf X ⟶
        (realSingularCochainOpenPresheafComplex X).X 0)
    (hη : η ≫ (realSingularCochainOpenPresheafComplex X).d 0 1 = 0) :
    ShortComplex (TopCat.Presheaf AddCommGrpCat.{v} X) :=
  { f := η
    g := (realSingularCochainOpenPresheafComplex X).d 0 1
    zero := hη }

/--
%%handwave
name:
  A stalked presheaf degree-zero augmented singular-cochain short complex from a chosen augmentation
statement:
  Taking a stalk of a chosen presheaf degree-zero augmented singular-cochain
  short complex gives a short complex of abelian groups.
proof:
  Apply the ordinary stalk functor to the chosen augmented short complex.
-/
abbrev realSingularCochainOpenPresheafAugmentationStalkShortComplexOf
    (X : TopCat.{v})
    (η :
      realConstantOpenPresheaf X ⟶
        (realSingularCochainOpenPresheafComplex X).X 0)
    (hη : η ≫ (realSingularCochainOpenPresheafComplex X).d 0 1 = 0)
    (x : X) :
    ShortComplex AddCommGrpCat.{v} :=
  @ShortComplex.map _ _ _ _ _ _
    (realSingularCochainOpenPresheafAugmentationShortComplexOf X η hη)
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x)
    (by infer_instance)

/--
%%handwave
name:
  Degree-zero singular chains are generated by singular vertices
statement:
  The degree-zero singular chain module of a space is the coproduct of one
  copy of the coefficient module for each singular zero-simplex.
proof:
  Unfold the singular chain complex as the alternating face complex of the
  simplicial object obtained from the singular simplicial set by replacing
  each simplex by a copy of the coefficient module.  In degree zero this is
  exactly the displayed coproduct.
-/
noncomputable def singularChainsDegreeZeroCoproductIso (T : TopCat.{v}) :
    (SingularChains ℝ T).X 0 ≅
      ∐ fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
        SingularCohomologyCoefficient.{0, v} ℝ := by
  unfold SingularChains AlgebraicTopology.singularChainComplexFunctor
    SSet.chainComplexFunctor
  exact Iso.refl _

/--
%%handwave
name:
  Singular chains in one degree are generated by singular simplices
statement:
  In every degree, the singular chain module of a space is the coproduct of
  one copy of the coefficient module for each singular simplex of that degree.
proof:
  Unfold the singular chain complex as the alternating face complex of the
  simplicial object obtained from the singular simplicial set by replacing
  each simplex by a copy of the coefficient module.  In the chosen degree this
  gives exactly the displayed coproduct.
-/
noncomputable def singularChainsDegreeCoproductIso (T : TopCat.{v}) (p : ℕ) :
    (SingularChains ℝ T).X p ≅
      ∐ fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk p)) =>
        SingularCohomologyCoefficient.{0, v} ℝ := by
  unfold SingularChains AlgebraicTopology.singularChainComplexFunctor
    SSet.chainComplexFunctor
  exact Iso.refl _

/--
%%handwave
name:
  Singular cochains are determined by their values on singular simplices
statement:
  If two singular \(p\)-cochains have the same value on every singular
  \(p\)-simplex, then they are equal.
proof:
  The singular \(p\)-chains form the coproduct of one copy of the coefficient
  module for each singular \(p\)-simplex.  A cochain is a morphism out of this
  coproduct, hence it is determined by its composites with all coproduct
  inclusions.
-/
theorem singularCochain_eq_of_forall_simplex_eval_eq
    (T : TopCat.{v}) (p : ℕ)
    (α β : (SingularCochainComplex ℝ T).X p)
    (hαβ :
      ∀ σ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk p)),
        Sigma.ι
            (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk p)) =>
              SingularCohomologyCoefficient.{0, v} ℝ) σ ≫
            (singularChainsDegreeCoproductIso T p).inv ≫ α =
          Sigma.ι
            (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk p)) =>
              SingularCohomologyCoefficient.{0, v} ℝ) σ ≫
            (singularChainsDegreeCoproductIso T p).inv ≫ β) :
    α = β := by
  have hcomp :
      (singularChainsDegreeCoproductIso T p).inv ≫ α =
        (singularChainsDegreeCoproductIso T p).inv ≫ β := by
    apply Sigma.hom_ext
    intro σ
    simpa [Category.assoc] using hαβ σ
  apply (cancel_epi (singularChainsDegreeCoproductIso T p).inv).1
  exact hcomp

/--
%%handwave
name:
  A singular cochain from values on singular simplices
statement:
  Assigning a coefficient-linear endomorphism to every singular
  \(p\)-simplex determines a singular \(p\)-cochain.
proof:
  The degree-\(p\) singular chains are the coproduct of one coefficient module
  for every singular \(p\)-simplex.  Use the universal property of this
  coproduct to define the linear functional.
-/
noncomputable def singularCochainOfSimplexEnd (T : TopCat.{v}) (p : ℕ)
    (φ :
      ∀ _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk p)),
        SingularCohomologyCoefficient.{0, v} ℝ ⟶
          SingularCohomologyCoefficient.{0, v} ℝ) :
    (SingularCochainComplex ℝ T).X p :=
  (singularChainsDegreeCoproductIso T p).hom ≫ Sigma.desc φ

/--
%%handwave
name:
  Evaluation of a cochain built from simplex values
statement:
  The singular cochain built from prescribed values on singular
  \(p\)-simplices has the prescribed value on each singular \(p\)-simplex.
proof:
  This is the coproduct-descending identity for the summand corresponding to
  the chosen singular simplex.
-/
theorem singularCochainOfSimplexEnd_eval (T : TopCat.{v}) (p : ℕ)
    (φ :
      ∀ _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk p)),
        SingularCohomologyCoefficient.{0, v} ℝ ⟶
          SingularCohomologyCoefficient.{0, v} ℝ)
    (σ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk p))) :
    Sigma.ι
        (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk p)) =>
          SingularCohomologyCoefficient.{0, v} ℝ) σ ≫
        (singularChainsDegreeCoproductIso T p).inv ≫
        singularCochainOfSimplexEnd T p φ =
      φ σ := by
  simp [singularCochainOfSimplexEnd]
  rw [Sigma.ι_desc]

/--
%%handwave
name:
  Evaluation of a pulled-back singular cochain at a singular simplex
statement:
  Evaluating the pullback of a singular \(p\)-cochain at a singular simplex is
  the same as evaluating the original cochain at the image singular simplex.
proof:
  In degree \(p\), singular chains are the coproduct over singular
  \(p\)-simplices.  Pullback of cochains is precomposition with the coproduct
  reindexing map induced by the continuous map on singular \(p\)-simplices.
-/
theorem singularCochain_eval_pullback {T S : TopCat.{v}}
    (p : ℕ) (f : T ⟶ S) (α : (SingularCochainComplex ℝ S).X p)
    (σ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk p))) :
    Sigma.ι
        (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk p)) =>
          SingularCohomologyCoefficient.{0, v} ℝ) σ ≫
        (singularChainsDegreeCoproductIso T p).inv ≫
        (singularCochainMap ℝ f).f p α =
      Sigma.ι
        (fun _ : (TopCat.toSSet.obj S).obj (op (SimplexCategory.mk p)) =>
          SingularCohomologyCoefficient.{0, v} ℝ)
        (((TopCat.toSSet.map f).app (op (SimplexCategory.mk p))) σ) ≫
        (singularChainsDegreeCoproductIso S p).inv ≫ α := by
  unfold singularCochainMap SingularCochainComplex SingularChains
    ChainComplex.linearYonedaObj
  dsimp [singularChainsDegreeCoproductIso,
    AlgebraicTopology.singularChainComplexFunctor,
    SSet.chainComplexFunctor]
  change
    (Sigma.ι
        (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk p)) =>
          SingularCohomologyCoefficient.{0, v} ℝ) σ ≫
        𝟙 (∐ fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk p)) =>
          SingularCohomologyCoefficient.{0, v} ℝ)) ≫
        (Sigma.map'
          ((TopCat.toSSet.map f).app (op (SimplexCategory.mk p)))
          (fun _ => 𝟙 (SingularCohomologyCoefficient.{0, v} ℝ)) ≫ α) =
      Sigma.ι
        (fun _ : (TopCat.toSSet.obj S).obj (op (SimplexCategory.mk p)) =>
          SingularCohomologyCoefficient.{0, v} ℝ)
        (((TopCat.toSSet.map f).app (op (SimplexCategory.mk p))) σ) ≫
        𝟙 (∐ fun _ : (TopCat.toSSet.obj S).obj (op (SimplexCategory.mk p)) =>
          SingularCohomologyCoefficient.{0, v} ℝ) ≫ α
  simp only [Category.comp_id, Category.id_comp]
  rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp]

/--
%%handwave
name:
  Open inclusions inject singular simplices
statement:
  If \(V\subset U\) are open subsets of a space, then the induced map from
  singular \(p\)-simplices in \(V\) to singular \(p\)-simplices in \(U\) is
  injective.
proof:
  The map of open subspaces is an inclusion, hence a monomorphism in
  topological spaces.  The singular simplicial set functor preserves
  monomorphisms, and monomorphisms of types are injective maps.
-/
theorem toSSet_openInclusion_app_injective
    (X : TopCat.{v}) (p : ℕ) {V U : Opens X} (hVU : V ≤ U) :
    Function.Injective
      (((TopCat.toSSet.map ((Opens.toTopCat X).map (homOfLE hVU))).app
        (op (SimplexCategory.mk p)))) := by
  let f : ((Opens.toTopCat X).obj V) ⟶ ((Opens.toTopCat X).obj U) :=
    (Opens.toTopCat X).map (homOfLE hVU)
  haveI : Mono f := by
    rw [TopCat.mono_iff_injective]
    intro x y hxy
    exact Subtype.ext (congrArg (fun z => z.1) hxy)
  haveI hSSet : Mono (TopCat.toSSet.map f) := by
    infer_instance
  have happMono : Mono ((TopCat.toSSet.map f).app (op (SimplexCategory.mk p))) :=
    (NatTrans.mono_iff_mono_app _).mp hSSet _
  exact (CategoryTheory.mono_iff_injective _).1 happMono

/--
%%handwave
name:
  Singular simplices as maps are natural in the target
statement:
  Under the identification of singular simplices with continuous maps from
  the standard simplex, applying a continuous map to a singular simplex is
  composition of continuous maps.
proof:
  This is the naturality built into the restricted Yoneda description of the
  singular simplicial set.
-/
theorem toSSetObjEquiv_map_apply
    {T S : TopCat.{v}} (f : T ⟶ S) (p : ℕ)
    (σ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk p))) :
    TopCat.toSSetObjEquiv S (op (SimplexCategory.mk p))
        (((TopCat.toSSet.map f).app (op (SimplexCategory.mk p))) σ) =
      f.hom.comp
        (TopCat.toSSetObjEquiv T (op (SimplexCategory.mk p)) σ) := by
  ext x
  rfl

/-- Singular \(p\)-simplices in an open subset. -/
abbrev openSingularSimplex (X : TopCat.{v}) (p : ℕ) (U : Opens X) : Type v :=
  (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).obj
    (op (SimplexCategory.mk p))

/-- The map on singular simplices induced by an inclusion of open subsets. -/
abbrev openSingularSimplexMap
    (X : TopCat.{v}) (p : ℕ) {V U : Opens X} (hVU : V ≤ U) :
    openSingularSimplex X p V → openSingularSimplex X p U :=
  ((TopCat.toSSet.map ((Opens.toTopCat X).map (homOfLE hVU))).app
    (op (SimplexCategory.mk p)))

/-- Evaluation of an ordinary open singular cochain on a singular simplex. -/
abbrev openSingularCochainSimplexEval
    (X : TopCat.{v}) (p : ℕ) (U : Opens X)
    (α : ((realSingularCochainOpenPresheafComplex X).X p).obj (op U))
    (σ : openSingularSimplex X p U) :
    SingularCohomologyCoefficient.{0, v} ℝ ⟶
      SingularCohomologyCoefficient.{0, v} ℝ :=
  Sigma.ι
      (fun _ : openSingularSimplex X p U =>
        SingularCohomologyCoefficient.{0, v} ℝ) σ ≫
    (singularChainsDegreeCoproductIso
      ((Opens.toTopCat X).obj U) p).inv ≫
    α

/--
%%handwave
name:
  Evaluation commutes with open restriction
statement:
  Restricting an ordinary singular cochain to a smaller open subset and
  evaluating it on a singular simplex is the same as evaluating the original
  cochain on the image simplex in the larger open subset.
proof:
  This is functoriality of singular cochains: restriction is pullback along
  the inclusion of open subspaces, and pullback evaluates by composing the
  simplex with that inclusion.
-/
theorem openSingularCochainSimplexEval_restrict
    (X : TopCat.{v}) (p : ℕ) {U V : Opens X} (hVU : V ≤ U)
    (α : ((realSingularCochainOpenPresheafComplex X).X p).obj (op U))
    (σ : openSingularSimplex X p V) :
    openSingularCochainSimplexEval X p V
        (((realSingularCochainOpenComplexFunctor X).map
          (homOfLE hVU).op).f p α) σ =
      openSingularCochainSimplexEval X p U α
        (openSingularSimplexMap X p hVU σ) := by
  have hpull :=
    singularCochain_eval_pullback
      (T := ((Opens.toTopCat X).obj V))
      (S := ((Opens.toTopCat X).obj U)) p
      ((Opens.toTopCat X).map (homOfLE hVU))
      α σ
  simpa [openSingularCochainSimplexEval, openSingularSimplexMap,
    realSingularCochainOpenPresheafComplex,
    realSingularCochainOpenComplexFunctor,
    realSingularCochainOpenModuleComplexFunctor,
    realSingularCochainModuleComplexFunctor,
    realSingularCochainComplexAddFunctor] using hpull

/--
%%handwave
name:
  Open singular cochains are determined by their values on singular simplices
statement:
  Two ordinary singular \(p\)-cochains on an open subset are equal if they
  have the same value on every singular \(p\)-simplex in that open subset.
proof:
  This is the preceding coproduct-generation statement for singular cochains,
  after viewing the open subset as a topological space.
-/
theorem realSingularCochainOpenPresheafComplex_eq_of_forall_simplex_eval_eq
    (X : TopCat.{v}) (p : ℕ) (U : Opens X)
    (α β : ((realSingularCochainOpenPresheafComplex X).X p).obj (op U))
    (hαβ :
      ∀ σ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).obj
          (op (SimplexCategory.mk p)),
        Sigma.ι
            (fun _ :
                (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).obj
                  (op (SimplexCategory.mk p)) =>
              SingularCohomologyCoefficient.{0, v} ℝ) σ ≫
            (singularChainsDegreeCoproductIso
              ((Opens.toTopCat X).obj U) p).inv ≫ α =
          Sigma.ι
            (fun _ :
                (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).obj
                  (op (SimplexCategory.mk p)) =>
              SingularCohomologyCoefficient.{0, v} ℝ) σ ≫
            (singularChainsDegreeCoproductIso
              ((Opens.toTopCat X).obj U) p).inv ≫ β) :
    α = β := by
  exact
    singularCochain_eq_of_forall_simplex_eval_eq
      ((Opens.toTopCat X).obj U) p α β hαβ

/--
%%handwave
name:
  Multiplication by a lifted real coefficient
statement:
  A lifted real number \(c\) defines an endomorphism of the lifted real
  coefficient module by multiplication by \(c\).
proof:
  Use scalar multiplication by the underlying real number on the lifted real
  coefficient module.
-/
def realSingularCohomologyCoefficientMulEnd (c : ULift.{v} ℝ) :
    SingularCohomologyCoefficient.{0, v} ℝ ⟶
      SingularCohomologyCoefficient.{0, v} ℝ :=
  ModuleCat.ofHom
    ((c.down : ℝ) •
      (LinearMap.id : (SingularCohomologyCoefficient.{0, v} ℝ) →ₗ[ℝ]
        SingularCohomologyCoefficient.{0, v} ℝ))
/--
%%handwave
name:
  Multiplication by zero on lifted real coefficients
statement:
  If \(M_c\) denotes multiplication by \(c\) on the lifted real coefficient
  module, then \(M_0=0\).
proof:
  Evaluate both endomorphisms at \(x\).  Their values agree because
  \(0\,x=0\).
-/
@[simp]
theorem realSingularCohomologyCoefficientMulEnd_zero :
    realSingularCohomologyCoefficientMulEnd (0 : ULift.{v} ℝ) = 0 := by
  ext x
  change (0 : ℝ) • x = 0
  exact zero_smul ℝ x
/--
%%handwave
name:
  Additivity of coefficient multiplication
statement:
  For lifted real numbers \(c,d\), multiplication on the lifted real
  coefficient module satisfies \(M_{c+d}=M_c+M_d\).
proof:
  Evaluate at \(x\) and use \((c+d)x=cx+dx\).
-/
theorem realSingularCohomologyCoefficientMulEnd_add
    (c d : ULift.{v} ℝ) :
    realSingularCohomologyCoefficientMulEnd (c + d) =
      realSingularCohomologyCoefficientMulEnd c +
        realSingularCohomologyCoefficientMulEnd d := by
  ext x
  cases c with
  | up c =>
  cases d with
  | up d =>
  change (c + d) • x = c • x + d • x
  exact add_smul c d x

/--
%%handwave
name:
  Endomorphisms of the lifted real coefficient module are scalar multiplications
statement:
  Every real-linear endomorphism of the lifted real coefficient module is
  multiplication by its value on \(1\).
proof:
  Every element of the lifted real line is a real scalar multiple of \(1\),
  and the endomorphism is real-linear.
-/
theorem realSingularCohomologyCoefficientEnd_eq_mulEnd_apply_one
    (φ : SingularCohomologyCoefficient.{0, v} ℝ ⟶
      SingularCohomologyCoefficient.{0, v} ℝ) :
    φ = realSingularCohomologyCoefficientMulEnd
      ((ModuleCat.Hom.hom φ) (ULift.up (1 : ℝ))) := by
  ext x
  cases x with
  | up x =>
    have hx : (ULift.up x : ULift.{v} ℝ) =
        x • (ULift.up (1 : ℝ) : ULift.{v} ℝ) := by
      ext
      simp
    rw [hx]
    calc
      (ModuleCat.Hom.hom φ) (x • (ULift.up (1 : ℝ) : ULift.{v} ℝ))
          = x • (ModuleCat.Hom.hom φ) (ULift.up (1 : ℝ)) := by
            exact (ModuleCat.Hom.hom φ).map_smul x (ULift.up (1 : ℝ))
      _ = (ModuleCat.Hom.hom
            (realSingularCohomologyCoefficientMulEnd
              ((ModuleCat.Hom.hom φ) (ULift.up (1 : ℝ)))))
            (x • (ULift.up (1 : ℝ) : ULift.{v} ℝ)) := by
            cases hφ1 : (ModuleCat.Hom.hom φ) (ULift.up (1 : ℝ)) with
            | up y =>
              change x • (ULift.up y : ULift.{v} ℝ) =
                y • (x • (ULift.up (1 : ℝ) : ULift.{v} ℝ))
              ext
              simp [mul_comm]

/--
%%handwave
name:
  A real constant as a singular zero-cochain
statement:
  A real constant \(c\) defines a singular zero-cochain on a space by sending
  every singular zero-simplex to \(c\).
proof:
  Identify degree-zero chains with the coproduct over singular vertices, and
  use the universal property of the coproduct with the same multiplication
  map on every summand.
-/
noncomputable def singularZeroCochainOfConstant (T : TopCat.{v})
    (c : ULift.{v} ℝ) :
    (SingularCochainComplex ℝ T).X 0 :=
  (singularChainsDegreeZeroCoproductIso T).hom ≫
    Sigma.desc
      (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
        realSingularCohomologyCoefficientMulEnd c)

/--
%%handwave
name:
  The zero constant gives the zero singular zero-cochain
statement:
  The singular zero-cochain associated to the constant \(0\) is zero.
proof:
  In the coproduct description of degree-zero chains, every summand map is
  multiplication by \(0\), hence is zero; therefore the coproduct-descended
  cochain is zero.
-/
theorem singularZeroCochainOfConstant_zero (T : TopCat.{v}) :
    singularZeroCochainOfConstant T (0 : ULift.{v} ℝ) = 0 := by
  unfold singularZeroCochainOfConstant
  rw [show
      Sigma.desc
        (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
          realSingularCohomologyCoefficientMulEnd (0 : ULift.{v} ℝ)) = 0 by
        apply Sigma.hom_ext
        intro j
        rw [Sigma.ι_desc, comp_zero,
          realSingularCohomologyCoefficientMulEnd_zero]]
  rw [comp_zero]
  rfl

/--
%%handwave
name:
  Constant singular zero-cochains are additive in the constant
statement:
  The singular zero-cochain associated to \(c+d\) is the sum of the singular
  zero-cochains associated to \(c\) and \(d\).
proof:
  In the coproduct description of degree-zero chains, multiplication by
  \(c+d\) is the sum of multiplication by \(c\) and multiplication by \(d\) on
  every summand.
-/
theorem singularZeroCochainOfConstant_add (T : TopCat.{v})
    (c d : ULift.{v} ℝ) :
    singularZeroCochainOfConstant T (c + d) =
      singularZeroCochainOfConstant T c +
        singularZeroCochainOfConstant T d := by
  unfold singularZeroCochainOfConstant
  rw [show
      Sigma.desc
        (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
          realSingularCohomologyCoefficientMulEnd (c + d)) =
        Sigma.desc
          (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
            realSingularCohomologyCoefficientMulEnd c) +
          Sigma.desc
            (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
              realSingularCohomologyCoefficientMulEnd d) by
        apply Sigma.hom_ext
        intro j
        rw [Sigma.ι_desc, Preadditive.comp_add, Sigma.ι_desc, Sigma.ι_desc,
          realSingularCohomologyCoefficientMulEnd_add]]
  rw [Preadditive.comp_add]
  rfl

/--
%%handwave
name:
  Constant singular zero-cochains are homogeneous in the constant
statement:
  Multiplying a constant singular zero-cochain by a real scalar gives the
  constant singular zero-cochain associated to the product constant.
proof:
  In the coproduct description of degree-zero chains, the statement reduces
  on every singular vertex summand to associativity of scalar multiplication.
-/
theorem singularZeroCochainOfConstant_smul (T : TopCat.{v})
    (r : ℝ) (c : ULift.{v} ℝ) :
    r • singularZeroCochainOfConstant T c =
      singularZeroCochainOfConstant T (ULift.up (r * c.down)) := by
  unfold singularZeroCochainOfConstant
  dsimp [singularChainsDegreeZeroCoproductIso]
  change
    r •
        (Sigma.desc
          (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
            realSingularCohomologyCoefficientMulEnd c)) =
      Sigma.desc
        (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
          realSingularCohomologyCoefficientMulEnd (ULift.up (r * c.down)))
  apply Sigma.hom_ext
  intro j
  calc
    Sigma.ι
          (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
            SingularCohomologyCoefficient.{0, v} ℝ) j ≫
        (r •
          Sigma.desc
            (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
              realSingularCohomologyCoefficientMulEnd c))
        = r •
            (Sigma.ι
                (fun _ :
                    (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
                  SingularCohomologyCoefficient.{0, v} ℝ) j ≫
              Sigma.desc
                (fun _ :
                    (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
                  realSingularCohomologyCoefficientMulEnd c)) := by
          exact CategoryTheory.Linear.comp_smul (R := ℝ) _ _ _ _ _ _
    _ = r • realSingularCohomologyCoefficientMulEnd c := by
          rw [Sigma.ι_desc]
    _ = realSingularCohomologyCoefficientMulEnd (ULift.up (r * c.down)) := by
          ext x
          change r • ((c.down : ℝ) • x) = (r * c.down) • x
          rw [mul_smul]
    _ =
        Sigma.ι
            (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
              SingularCohomologyCoefficient.{0, v} ℝ) j ≫
          Sigma.desc
            (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
              realSingularCohomologyCoefficientMulEnd
                (ULift.up (r * c.down))) := by
          rw [Sigma.ι_desc]

/--
%%handwave
name:
  Pullback preserves constant singular zero-cochains
statement:
  Pulling a constant singular zero-cochain back along a continuous map gives
  the constant singular zero-cochain with the same constant.
proof:
  After unfolding singular chains in degree zero, the chain map is the
  coproduct reindexing map induced by the map on singular vertices.  Composing
  this reindexing map with a coproduct-descended cochain that is the same on
  every vertex summand leaves the cochain unchanged.
-/
theorem singularZeroCochainOfConstant_pullback {T S : TopCat.{v}}
    (f : T ⟶ S) (c : ULift.{v} ℝ) :
    (singularCochainMap ℝ f).f 0 (singularZeroCochainOfConstant S c) =
      singularZeroCochainOfConstant T c := by
  unfold singularCochainMap SingularCochainComplex SingularChains
    ChainComplex.linearYonedaObj singularZeroCochainOfConstant
  dsimp [singularChainsDegreeZeroCoproductIso,
    AlgebraicTopology.singularChainComplexFunctor,
    SSet.chainComplexFunctor]
  change
    Sigma.map'
        ((TopCat.toSSet.map f).app (op (SimplexCategory.mk 0)))
        (fun _ => 𝟙 (SingularCohomologyCoefficient.{0, v} ℝ)) ≫
      Sigma.desc
        (fun _ : (TopCat.toSSet.obj S).obj (op (SimplexCategory.mk 0)) =>
          realSingularCohomologyCoefficientMulEnd c) =
    Sigma.desc
      (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
        realSingularCohomologyCoefficientMulEnd c)
  apply Sigma.hom_ext
  intro j
  rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp, Sigma.ι_desc,
    Sigma.ι_desc]

/--
%%handwave
name:
  Evaluation of a pulled-back singular zero-cochain at a vertex
statement:
  Evaluating the pullback of a singular zero-cochain at a singular vertex is
  the same as evaluating the original zero-cochain at the image vertex.
proof:
  In degree zero, singular chains are the coproduct over singular vertices.
  Pullback of zero-cochains is precomposition with the coproduct reindexing
  map induced by the continuous map on vertices.
-/
theorem singularZeroCochain_eval_pullback {T S : TopCat.{v}}
    (f : T ⟶ S) (α : (SingularCochainComplex ℝ S).X 0)
    (t : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0))) :
    Sigma.ι
        (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
          SingularCohomologyCoefficient.{0, v} ℝ) t ≫
        (singularChainsDegreeZeroCoproductIso T).inv ≫
        (singularCochainMap ℝ f).f 0 α =
      Sigma.ι
        (fun _ : (TopCat.toSSet.obj S).obj (op (SimplexCategory.mk 0)) =>
          SingularCohomologyCoefficient.{0, v} ℝ)
        (((TopCat.toSSet.map f).app (op (SimplexCategory.mk 0))) t) ≫
        (singularChainsDegreeZeroCoproductIso S).inv ≫ α := by
  unfold singularCochainMap SingularCochainComplex SingularChains
    ChainComplex.linearYonedaObj
  dsimp [singularChainsDegreeZeroCoproductIso,
    AlgebraicTopology.singularChainComplexFunctor,
    SSet.chainComplexFunctor]
  change
    (Sigma.ι
        (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
          SingularCohomologyCoefficient.{0, v} ℝ) t ≫
        𝟙 (∐ fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
          SingularCohomologyCoefficient.{0, v} ℝ)) ≫
        (Sigma.map'
          ((TopCat.toSSet.map f).app (op (SimplexCategory.mk 0)))
          (fun _ => 𝟙 (SingularCohomologyCoefficient.{0, v} ℝ)) ≫ α) =
      Sigma.ι
        (fun _ : (TopCat.toSSet.obj S).obj (op (SimplexCategory.mk 0)) =>
          SingularCohomologyCoefficient.{0, v} ℝ)
        (((TopCat.toSSet.map f).app (op (SimplexCategory.mk 0))) t) ≫
        𝟙 (∐ fun _ : (TopCat.toSSet.obj S).obj (op (SimplexCategory.mk 0)) =>
          SingularCohomologyCoefficient.{0, v} ℝ) ≫ α
  simp only [Category.comp_id, Category.id_comp]
  rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp]

/--
%%handwave
name:
  Singular zero-cochains are determined by their values on vertices
statement:
  If a singular zero-cochain evaluates to zero on every singular vertex, then
  the zero-cochain is zero.
proof:
  In degree zero, singular chains are the coproduct over singular vertices.
  A zero-cochain is a morphism out of this coproduct, hence is determined by
  its composites with the coproduct inclusions.
-/
theorem singularZeroCochain_eq_zero_of_forall_vertex_eval_zero
    (T : TopCat.{v}) (α : (SingularCochainComplex ℝ T).X 0)
    (hα :
      ∀ t : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)),
        Sigma.ι
            (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
              SingularCohomologyCoefficient.{0, v} ℝ) t ≫
            (singularChainsDegreeZeroCoproductIso T).inv ≫ α = 0) :
    α = 0 := by
  have hcomp :
      (singularChainsDegreeZeroCoproductIso T).inv ≫ α = 0 := by
    apply Sigma.hom_ext
    intro t
    simpa [Category.assoc] using hα t
  apply (cancel_epi (singularChainsDegreeZeroCoproductIso T).inv).1
  simpa using hcomp

/--
%%handwave
name:
  Pullback along a constant map gives a constant singular zero-cochain
statement:
  Pulling an arbitrary singular zero-cochain back along a constant map gives
  a constant singular zero-cochain on the source.
proof:
  In the degree-zero coproduct model, the constant map sends every singular
  vertex of the source to the chosen vertex of the target.  The pullback is
  therefore the same coefficient endomorphism on every source vertex, and
  every such endomorphism of the real coefficient module is multiplication by
  its value on \(1\).
-/
theorem singularCochainMap_const_zero_eq_singularZeroCochainOfConstant
    (T S : TopCat.{v}) (y : S)
    (α : (SingularCochainComplex ℝ S).X 0) :
    ∃ c : ULift.{v} ℝ,
      (singularCochainMap ℝ (TopCat.const (X := T) y)).f 0 α =
        singularZeroCochainOfConstant T c := by
  let y₀ : (TopCat.toSSet.obj S).obj (op (SimplexCategory.mk 0)) :=
    TopCat.toSSetObj₀Equiv.symm y
  let evalAtY : SingularCohomologyCoefficient.{0, v} ℝ ⟶
      SingularCohomologyCoefficient.{0, v} ℝ :=
    Sigma.ι
        (fun _ : (TopCat.toSSet.obj S).obj (op (SimplexCategory.mk 0)) =>
          SingularCohomologyCoefficient.{0, v} ℝ) y₀ ≫
      (singularChainsDegreeZeroCoproductIso S).inv ≫ α
  refine ⟨(ModuleCat.Hom.hom evalAtY) (ULift.up (1 : ℝ)), ?_⟩
  unfold singularCochainMap SingularCochainComplex SingularChains
    ChainComplex.linearYonedaObj singularZeroCochainOfConstant
  dsimp [singularChainsDegreeZeroCoproductIso,
    AlgebraicTopology.singularChainComplexFunctor,
    SSet.chainComplexFunctor]
  change
    Sigma.map'
        ((TopCat.toSSet.map (TopCat.const (X := T) y)).app
          (op (SimplexCategory.mk 0)))
        (fun _ => 𝟙 (SingularCohomologyCoefficient.{0, v} ℝ)) ≫ α =
      Sigma.desc
        (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
          realSingularCohomologyCoefficientMulEnd
            ((ModuleCat.Hom.hom evalAtY) (ULift.up (1 : ℝ))))
  apply Sigma.hom_ext
  intro t
  rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp, Sigma.ι_desc]
  have ht :
      ((TopCat.toSSet.map (TopCat.const (X := T) y)).app
          (op (SimplexCategory.mk 0))) t = y₀ := by
    simp [y₀]
  rw [ht]
  exact realSingularCohomologyCoefficientEnd_eq_mulEnd_apply_one _

/--
%%handwave
name:
  Constant singular zero-cochains are closed on a space
statement:
  The first singular coboundary of a constant singular zero-cochain is zero.
proof:
  In degree one, the singular chain differential is the alternating sum of
  the two endpoint face maps.  Each endpoint face map followed by the
  constant zero-cochain gives the same constant cochain on singular
  one-simplices, so the two terms cancel.
-/
theorem singularZeroCochainOfConstant_closed (T : TopCat.{v})
    (c : ULift.{v} ℝ) :
    (SingularCochainComplex ℝ T).d 0 1
        (singularZeroCochainOfConstant T c) = 0 := by
  let A : SimplicialObject (ModuleCat.{v} ℝ) :=
    (((SimplicialObject.whiskering (Type v) (ModuleCat.{v} ℝ)).obj
      (sigmaConst.obj (SingularCohomologyCoefficient.{0, v} ℝ))).obj
        (TopCat.toSSet.obj T))
  unfold SingularCochainComplex SingularChains ChainComplex.linearYonedaObj
    singularZeroCochainOfConstant
  dsimp [singularChainsDegreeZeroCoproductIso,
    AlgebraicTopology.singularChainComplexFunctor,
    SSet.chainComplexFunctor]
  change (((AlgebraicTopology.alternatingFaceMapComplex
      (ModuleCat.{v} ℝ)).obj A).d 1 0) ≫
      Sigma.desc
        (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
          realSingularCohomologyCoefficientMulEnd c) = 0
  let desc0 :
      (∐ fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
        SingularCohomologyCoefficient.{0, v} ℝ) ⟶
        SingularCohomologyCoefficient.{0, v} ℝ :=
    Sigma.desc
      (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
        realSingularCohomologyCoefficientMulEnd c)
  let desc1 :
      (∐ fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 1)) =>
        SingularCohomologyCoefficient.{0, v} ℝ) ⟶
        SingularCohomologyCoefficient.{0, v} ℝ :=
    Sigma.desc
      (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 1)) =>
        realSingularCohomologyCoefficientMulEnd c)
  change (((AlgebraicTopology.alternatingFaceMapComplex
      (ModuleCat.{v} ℝ)).obj A).d 1 0) ≫ desc0 = 0
  have hδ (i : Fin 2) : A.δ i ≫ desc0 = desc1 := by
    subst A
    subst desc0
    subst desc1
    change
      Sigma.map'
          (SimplicialObject.δ (TopCat.toSSet.obj T) i)
          (fun _ => 𝟙 (SingularCohomologyCoefficient.{0, v} ℝ)) ≫
        Sigma.desc
          (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
            realSingularCohomologyCoefficientMulEnd c) =
      Sigma.desc
        (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 1)) =>
          realSingularCohomologyCoefficientMulEnd c)
    apply Sigma.hom_ext
    intro j
    rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp, Sigma.ι_desc,
      Sigma.ι_desc]
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  change (AlgebraicTopology.AlternatingFaceMapComplex.objD A 0) ≫ desc0 = 0
  rw [AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul]
  rw [Preadditive.add_comp, Preadditive.zsmul_comp, hδ 0, hδ 1]
  norm_num

/--
%%handwave
name:
  A zero constant singular zero-cochain has zero constant on a nonempty space
statement:
  On a nonempty space, if the singular zero-cochain associated to a real
  constant is zero, then the real constant is zero.
proof:
  Evaluate the zero-cochain on one singular vertex.  In the coproduct model
  of degree-zero chains, this recovers multiplication by the constant on the
  coefficient module; applying it to \(1\) recovers the constant itself.
-/
theorem singularZeroCochainOfConstant_eq_zero_of_nonempty
    (T : TopCat.{v}) [Nonempty T] (c : ULift.{v} ℝ)
    (h : singularZeroCochainOfConstant T c = 0) : c = 0 := by
  let vertex : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) :=
    TopCat.toSSetObj₀Equiv.symm (Classical.choice (inferInstance : Nonempty T))
  have hmul : realSingularCohomologyCoefficientMulEnd c = 0 := by
    have hcongr := congrArg
      (fun φ =>
        Sigma.ι
            (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
              SingularCohomologyCoefficient.{0, v} ℝ) vertex ≫
          (singularChainsDegreeZeroCoproductIso T).inv ≫ φ) h
    simpa [singularZeroCochainOfConstant, vertex, Category.assoc, Sigma.ι_desc]
      using hcongr
  cases c with
  | up r =>
    have happ := congrArg
      (fun φ : SingularCohomologyCoefficient.{0, v} ℝ ⟶
          SingularCohomologyCoefficient.{0, v} ℝ =>
        (ModuleCat.Hom.hom φ) (ULift.up (1 : ℝ))) hmul
    change r • (ULift.up (1 : ℝ) : ULift.{v} ℝ) = 0 at happ
    have hr : r = 0 := by
      change ULift.up (r * 1) = (0 : ULift.{v} ℝ) at happ
      simpa using congrArg ULift.down happ
    ext
    simp [hr]

/--
%%handwave
name:
  Constant singular zero-cochains restrict to constant singular zero-cochains
statement:
  Restricting the singular zero-cochain associated to a real constant along
  an inclusion of open subsets gives the singular zero-cochain associated to
  the same constant on the smaller open subset.
proof:
  Naturality of the degree-zero coproduct description sends a singular vertex
  of the smaller open subset to the same vertex regarded in the larger open
  subset, and all vertex summands carry the same coefficient map.
-/
theorem singularZeroCochainOfConstant_openRestriction
    (X : TopCat.{v}) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (c : (realConstantOpenPresheaf X).obj U) :
    ((realSingularCochainOpenPresheafComplex X).X 0).map f
        (singularZeroCochainOfConstant ((Opens.toTopCat X).obj (unop U)) c) =
      singularZeroCochainOfConstant ((Opens.toTopCat X).obj (unop V))
        ((realConstantOpenPresheaf X).map f c) := by
  simpa [realSingularCochainOpenPresheafComplex,
    realSingularCochainOpenComplexFunctor, realSingularCochainOpenModuleComplexFunctor,
    realSingularCochainComplexAddFunctor, realConstantOpenPresheaf] using
      singularZeroCochainOfConstant_pullback
        ((Opens.toTopCat X).map f.unop) c

/--
%%handwave
name:
  The standard constant-to-zero-cochain presheaf map
statement:
  The maps sending a real constant on each open subset to the corresponding
  constant singular zero-cochain form a natural transformation from the
  constant real presheaf to the presheaf of singular zero-cochains.
proof:
  Additivity follows from additivity of multiplication by constants on each
  degree-zero chain summand.  Naturality is the compatibility of constant
  singular zero-cochains with restriction.
-/
noncomputable def standardRealConstantOpenPresheafToSingularCochainZeroPresheaf
    (X : TopCat.{v}) :
    realConstantOpenPresheaf X ⟶
      (realSingularCochainOpenPresheafComplex X).X 0 where
  app U :=
    AddCommGrpCat.ofHom
      { toFun := fun c =>
          singularZeroCochainOfConstant ((Opens.toTopCat X).obj (unop U)) c
        map_zero' := by
          exact singularZeroCochainOfConstant_zero
            ((Opens.toTopCat X).obj (unop U))
        map_add' := by
          intro c d
          exact singularZeroCochainOfConstant_add
            ((Opens.toTopCat X).obj (unop U)) c d }
  naturality {U V} f := by
    ext c
    exact (singularZeroCochainOfConstant_openRestriction X f c).symm

/--
%%handwave
name:
  Constant singular zero-cochains are closed
statement:
  The standard constant-to-zero-cochain map is killed by the first singular
  coboundary.
proof:
  The coboundary of a constant zero-cochain evaluates a singular one-simplex
  by subtracting the same value at its two endpoints.
-/
theorem standardRealConstantOpenPresheafToSingularCochainZeroPresheaf_comp_d
    (X : TopCat.{v}) :
    standardRealConstantOpenPresheafToSingularCochainZeroPresheaf X ≫
        (realSingularCochainOpenPresheafComplex X).d 0 1 = 0 := by
  ext U c
  simpa [standardRealConstantOpenPresheafToSingularCochainZeroPresheaf,
    realSingularCochainOpenPresheafComplex, realSingularCochainOpenComplexFunctor,
    realSingularCochainOpenModuleComplexFunctor, realSingularCochainComplexAddFunctor]
    using singularZeroCochainOfConstant_closed ((Opens.toTopCat X).obj U) c

/--
%%handwave
name:
  The standard constant-to-zero-cochain map commutes with scalar multiplication
statement:
  Multiplying a constant before forming its singular zero-cochain agrees with
  forming the singular zero-cochain and then multiplying it as a cochain.
proof:
  On every singular vertex summand, both maps are multiplication by the
  product of the two real scalars.
-/
theorem standardRealConstantOpenPresheafToSingularCochainZeroPresheaf_scalar
    (X : TopCat.{v}) (r : ℝ) :
    standardRealConstantOpenPresheafToSingularCochainZeroPresheaf X ≫
        (realSingularCochainOpenPresheafComplexScalarEnd X r).f 0 =
      realConstantOpenPresheafScalarEnd X r ≫
        standardRealConstantOpenPresheafToSingularCochainZeroPresheaf X := by
  ext U c
  simpa [standardRealConstantOpenPresheafToSingularCochainZeroPresheaf,
    realSingularCochainOpenPresheafComplexScalarEnd,
    realSingularCochainOpenComplexFunctorScalarNatTrans,
    realConstantOpenPresheafScalarEnd,
    realULiftScalarAddMonoidHom] using
      (singularZeroCochainOfConstant_smul
        ((Opens.toTopCat X).obj U) r c)

private lemma complexShape_symm_next_eq_prev_for_singularCohomology
    {ι : Type*} (c : ComplexShape ι) (i : ι) :
    c.symm.next i = c.prev i := by
  by_cases h : ∃ j, c.Rel j i
  · rcases h with ⟨j, hj⟩
    exact ((c.symm).next_eq' hj).trans ((c.prev_eq' hj).symm)
  · have hprev : c.prev i = i := by
      exact c.prev_eq_self' i (by simpa using h)
    have hnext : c.symm.next i = i := by
      exact (c.symm).next_eq_self' i (by simpa [ComplexShape.symm] using h)
    exact hnext.trans hprev.symm

private lemma complexShape_symm_prev_eq_next_for_singularCohomology
    {ι : Type*} (c : ComplexShape ι) (i : ι) :
    c.symm.prev i = c.next i := by
  simpa using (complexShape_symm_next_eq_prev_for_singularCohomology c.symm i).symm

private theorem homotopy_unopFunctor_map_op_for_singularCohomology
    {V : Type*} [Category* V] [Preadditive V] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex Vᵒᵖ c} {f g : K ⟶ L}
    (H : _root_.Homotopy f g) :
    Nonempty
      (_root_.Homotopy
        ((HomologicalComplex.unopFunctor V c).map f.op)
        ((HomologicalComplex.unopFunctor V c).map g.op)) := by
  refine ⟨?_⟩
  refine
    { hom := fun i j => (H.hom j i).unop
      zero := ?_
      comm := ?_ }
  · intro i j hij
    simpa using congrArg Quiver.Hom.unop (H.zero j i hij)
  · intro i
    have h := congrArg Quiver.Hom.unop (H.comm i)
    dsimp [dNext, prevD, fromNext, toPrev] at h ⊢
    change (f.f i).unop =
      ((L.d (c.symm.next i) i).unop ≫
          (H.hom i (c.symm.next i)).unop +
        (H.hom (c.symm.prev i) i).unop ≫
          (K.d i (c.symm.prev i)).unop) +
        (g.f i).unop
    simpa [complexShape_symm_next_eq_prev_for_singularCohomology,
      complexShape_symm_prev_eq_next_for_singularCohomology, unop_add, add_assoc,
      add_comm, add_left_comm] using h

private theorem singularCochainMap_homotopy_of_chainHomotopy_for_singularCohomology
    (R : Type u) [CommRing R] {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (H :
      _root_.Homotopy
        (((AlgebraicTopology.singularChainComplexFunctor
              (ModuleCat.{max u v} R)).obj
            (SingularCohomologyCoefficient.{u, v} R)).map f)
        (((AlgebraicTopology.singularChainComplexFunctor
              (ModuleCat.{max u v} R)).obj
            (SingularCohomologyCoefficient.{u, v} R)).map g)) :
    Nonempty (_root_.Homotopy (singularCochainMap R f) (singularCochainMap R g)) := by
  let F :=
    (((linearYoneda R (ModuleCat.{max u v} R)).obj
      (SingularCohomologyCoefficient.{u, v} R)).rightOp)
  have Hdual :
      _root_.Homotopy
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (((AlgebraicTopology.singularChainComplexFunctor
                (ModuleCat.{max u v} R)).obj
              (SingularCohomologyCoefficient.{u, v} R)).map f))
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (((AlgebraicTopology.singularChainComplexFunctor
                (ModuleCat.{max u v} R)).obj
              (SingularCohomologyCoefficient.{u, v} R)).map g)) :=
    F.mapHomotopy H
  simpa [F, singularCochainMap] using
    homotopy_unopFunctor_map_op_for_singularCohomology
      (V := ModuleCat.{max u v} R)
      (c := ComplexShape.down ℕ)
      Hdual

/--
%%handwave
name:
  Homotopic maps agree on closed singular zero-cochains
statement:
  If two maps of spaces are homotopic, then their pullbacks agree on closed
  real singular zero-cochains.
proof:
  Apply the cochain homotopy induced by the topological homotopy.  In degree
  zero the homotopy formula has no incoming boundary term, so the difference
  of the two pullbacks of a closed zero-cochain is zero.
-/
theorem singularCochainMap_eq_on_closed_zero_of_homotopy
    {T S : TopCat.{v}} {f g : T ⟶ S} (H : TopCat.Homotopy f g)
    (α : (SingularCochainComplex ℝ S).X 0)
    (hα : (SingularCochainComplex ℝ S).d 0 1 α = 0) :
    (singularCochainMap ℝ f).f 0 α =
      (singularCochainMap ℝ g).f 0 α := by
  change (ModuleCat.Hom.hom ((singularCochainMap ℝ f).f 0)) α =
    (ModuleCat.Hom.hom ((singularCochainMap ℝ g).f 0)) α
  rcases singularCochainMap_homotopy_of_chainHomotopy_for_singularCohomology ℝ
      (H.singularChainComplexFunctorObjMap
        (SingularCohomologyCoefficient.{0, v} ℝ)) with
    ⟨h⟩
  have hclosed :
      (ModuleCat.Hom.hom ((SingularCochainComplex ℝ S).d 0 (0 + 1))) α = 0 := by
    simpa using hα
  have hcomm := h.comm 0
  have hcomm_apply := congrArg (fun φ => (ModuleCat.Hom.hom φ) α) hcomm
  rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex] at hcomm_apply
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_zero,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at hcomm_apply
  rw [hclosed] at hcomm_apply
  simp only [map_zero, zero_add] at hcomm_apply
  simpa using hcomm_apply

/--
%%handwave
name:
  Closed singular zero-cochains restrict to constants over null-homotopic inclusions
statement:
  If \(V\subset U\) is an open inclusion whose associated map is
  null-homotopic, then the restriction to \(V\) of a closed singular
  zero-cochain on \(U\) is in the image of the standard constant
  zero-cochain map on \(V\).
proof:
  A closed zero-cochain is constant along singular one-simplices.  The
  null-homotopy joins every point of \(V\) to the contraction point inside
  \(U\), so the restricted zero-cochain has the same value on every singular
  vertex of \(V\).
-/
theorem standardRealConstantOpenPresheafToSingularCochainZeroPresheaf_local_constant
    (X : TopCat.{v}) {U V : Opens X} (hVU : V ≤ U)
    (hnull : (((Opens.toTopCat X).map (homOfLE hVU)).hom).Nullhomotopic)
    (α : (SingularCochainComplex ℝ ((Opens.toTopCat X).obj U)).X 0)
    (hα :
      (SingularCochainComplex ℝ ((Opens.toTopCat X).obj U)).d 0 1 α = 0) :
    ∃ c : (realConstantOpenPresheaf X).obj (Opposite.op V),
      (singularCochainMap ℝ ((Opens.toTopCat X).map (homOfLE hVU))).f 0 α =
        (standardRealConstantOpenPresheafToSingularCochainZeroPresheaf X).app
          (Opposite.op V) c := by
  rcases hnull with ⟨y, ⟨H⟩⟩
  have heq :
      (singularCochainMap ℝ ((Opens.toTopCat X).map (homOfLE hVU))).f 0 α =
        (singularCochainMap ℝ
          (TopCat.const (X := (Opens.toTopCat X).obj V) y)).f 0 α :=
    singularCochainMap_eq_on_closed_zero_of_homotopy H α hα
  rcases singularCochainMap_const_zero_eq_singularZeroCochainOfConstant
      ((Opens.toTopCat X).obj V) ((Opens.toTopCat X).obj U) y α with
    ⟨c, hc⟩
  refine ⟨c, heq.trans ?_⟩
  simpa [standardRealConstantOpenPresheafToSingularCochainZeroPresheaf] using hc

/--
%%handwave
name:
  The standard constant-to-zero-cochain map is injective on constant germs
statement:
  If the germ of the standard singular zero-cochain associated to a constant
  real germ is zero, then the original constant real germ is zero.
proof:
  Evaluate the zero-cochain germ on the constant singular zero-simplex at the
  base point.  This recovers the representing real constant.
-/
theorem standardRealConstantOpenPresheafToSingularCochainZeroPresheaf_germ_eq_zero
    (X : TopCat.{v}) (x : X) (U : Opens X) (hxU : x ∈ U)
    (c : (realConstantOpenPresheaf X).obj (Opposite.op U))
    (himage :
      ((realSingularCochainOpenPresheafComplex X).X 0).germ U x hxU
        ((standardRealConstantOpenPresheafToSingularCochainZeroPresheaf X).app
          (Opposite.op U) c) = 0) :
    (realConstantOpenPresheaf X).germ U x hxU c = 0 := by
  let P₀ : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X 0
  let aug : realConstantOpenPresheaf X ⟶ P₀ :=
    standardRealConstantOpenPresheafToSingularCochainZeroPresheaf X
  have hzero_germ :
      P₀.germ U x hxU (aug.app (Opposite.op U) c) =
        P₀.germ U x hxU 0 := by
    simpa [P₀, aug] using himage
  rcases P₀.germ_eq x hxU hxU (aug.app (Opposite.op U) c) 0 hzero_germ with
    ⟨W, hxW, iWU, iWU', heq⟩
  have hleft :
      P₀.map iWU.op (aug.app (Opposite.op U) c) =
        aug.app (Opposite.op W) ((realConstantOpenPresheaf X).map iWU.op c) := by
    have hn := aug.naturality iWU.op
    change
      (ConcreteCategory.hom (P₀.map iWU.op)) (aug.app (Opposite.op U) c) =
        (ConcreteCategory.hom (aug.app (Opposite.op W)))
          (((realConstantOpenPresheaf X).map iWU.op) c)
    simpa [ConcreteCategory.comp_apply] using
      congrArg (fun φ => (ConcreteCategory.hom φ) c) hn.symm
  have hconst_zero :
      aug.app (Opposite.op W) ((realConstantOpenPresheaf X).map iWU.op c) = 0 := by
    rw [← hleft]
    exact heq.trans ((P₀.map iWU'.op).hom.map_zero)
  have hc_restrict_zero : (realConstantOpenPresheaf X).map iWU.op c = 0 := by
    haveI : Nonempty ((Opens.toTopCat X).obj W) := ⟨⟨x, hxW⟩⟩
    exact singularZeroCochainOfConstant_eq_zero_of_nonempty
      ((Opens.toTopCat X).obj W) ((realConstantOpenPresheaf X).map iWU.op c)
      (by simpa [aug, standardRealConstantOpenPresheafToSingularCochainZeroPresheaf]
        using hconst_zero)
  have hc : c = 0 := by
    simpa [realConstantOpenPresheaf] using hc_restrict_zero
  rw [hc]
  exact ((realConstantOpenPresheaf X).germ U x hxU).hom.map_zero

/--
%%handwave
name:
  Constants define singular zero-cochains on open subsets
statement:
  There is a natural map from the constant real presheaf to the presheaf of
  singular zero-cochains.  It sends a real number \(c\) to the zero-cochain
  which takes value \(c\) on every singular zero-simplex.  This zero-cochain
  is closed, and the construction commutes with scalar multiplication.
proof:
  On an open set \(U\), define the zero-cochain by evaluation \( \sigma
  \mapsto c\) on singular zero-simplices \(\sigma:\Delta^0\to U\).  Its
  coboundary is zero because the two endpoint evaluations of a singular
  one-simplex are both \(c\).  Naturality under restriction and scalar
  compatibility are immediate from the formula.
-/
theorem exists_realConstantOpenPresheafToSingularCochainZeroPresheaf_with_formula
    (X : TopCat.{v}) :
    ∃ η :
        realConstantOpenPresheaf X ⟶
          (realSingularCochainOpenPresheafComplex X).X 0,
      ∃ _ : η ≫ (realSingularCochainOpenPresheafComplex X).d 0 1 = 0,
        (∀ r : ℝ,
          η ≫ (realSingularCochainOpenPresheafComplexScalarEnd X r).f 0 =
            realConstantOpenPresheafScalarEnd X r ≫ η) ∧
        (∀ {U V : Opens X} (hVU : V ≤ U)
          (_hnull : (((Opens.toTopCat X).map (homOfLE hVU)).hom).Nullhomotopic)
          (α : (SingularCochainComplex ℝ ((Opens.toTopCat X).obj U)).X 0),
          (SingularCochainComplex ℝ ((Opens.toTopCat X).obj U)).d 0 1 α = 0 →
            ∃ c : (realConstantOpenPresheaf X).obj (Opposite.op V),
              (singularCochainMap ℝ ((Opens.toTopCat X).map (homOfLE hVU))).f 0 α =
                η.app (Opposite.op V) c) ∧
        (∀ (x : X) (U : Opens X) (hxU : x ∈ U)
          (c : (realConstantOpenPresheaf X).obj (Opposite.op U)),
          ((realSingularCochainOpenPresheafComplex X).X 0).germ U x hxU
              (η.app (Opposite.op U) c) = 0 →
            (realConstantOpenPresheaf X).germ U x hxU c = 0) := by
  exact
    ⟨standardRealConstantOpenPresheafToSingularCochainZeroPresheaf X,
      standardRealConstantOpenPresheafToSingularCochainZeroPresheaf_comp_d X,
      standardRealConstantOpenPresheafToSingularCochainZeroPresheaf_scalar X,
      standardRealConstantOpenPresheafToSingularCochainZeroPresheaf_local_constant X,
      standardRealConstantOpenPresheafToSingularCochainZeroPresheaf_germ_eq_zero X⟩
/--
%%handwave
name:
  Scalar-compatible singular zero-cochain augmentation
statement:
  For every space \(X\), there is a natural morphism
  \(\eta\colon\underline{\mathbb R}\to C^0(-;\mathbb R)\) such that
  \(d\circ\eta=0\) and, for every \(r\in\mathbb R\),
  \(M_r\circ\eta=\eta\circ S_r\), where \(M_r\) and \(S_r\) are multiplication by
  \(r\) on singular cochains and on the constant presheaf, respectively.
proof:
  [Choose the natural map sending a constant \(c\) to the zero-cochain with value \(c\) at every singular vertex; it is closed and commutes with scalar multiplication.](lean:JJMath.Cohomology.exists_realConstantOpenPresheafToSingularCochainZeroPresheaf_with_formula)
-/
theorem exists_realConstantOpenPresheafToSingularCochainZeroPresheaf
    (X : TopCat.{v}) :
    ∃ η :
        realConstantOpenPresheaf X ⟶
          (realSingularCochainOpenPresheafComplex X).X 0,
      ∃ _ : η ≫ (realSingularCochainOpenPresheafComplex X).d 0 1 = 0,
        ∀ r : ℝ,
          η ≫ (realSingularCochainOpenPresheafComplexScalarEnd X r).f 0 =
            realConstantOpenPresheafScalarEnd X r ≫ η := by
  rcases exists_realConstantOpenPresheafToSingularCochainZeroPresheaf_with_formula
      (X := X) with
    ⟨η, hη, hscalar, _hlocal_constant, _hgerm_zero⟩
  exact ⟨η, hη, hscalar⟩

/-- The standard map from constants to singular zero-cochains on open subsets. -/
noncomputable def realConstantOpenPresheafToSingularCochainZeroPresheaf
    (X : TopCat.{v}) :
    realConstantOpenPresheaf X ⟶
      (realSingularCochainOpenPresheafComplex X).X 0 :=
  standardRealConstantOpenPresheafToSingularCochainZeroPresheaf X

private theorem realConstantOpenPresheafToSingularCochainZeroPresheaf_full_spec
    (X : TopCat.{v}) :
    ∃ _ :
        realConstantOpenPresheafToSingularCochainZeroPresheaf X ≫
          (realSingularCochainOpenPresheafComplex X).d 0 1 = 0,
      (∀ r : ℝ,
        realConstantOpenPresheafToSingularCochainZeroPresheaf X ≫
            (realSingularCochainOpenPresheafComplexScalarEnd X r).f 0 =
          realConstantOpenPresheafScalarEnd X r ≫
            realConstantOpenPresheafToSingularCochainZeroPresheaf X) ∧
      (∀ {U V : Opens X} (hVU : V ≤ U)
        (_hnull : (((Opens.toTopCat X).map (homOfLE hVU)).hom).Nullhomotopic)
        (α : (SingularCochainComplex ℝ ((Opens.toTopCat X).obj U)).X 0),
        (SingularCochainComplex ℝ ((Opens.toTopCat X).obj U)).d 0 1 α = 0 →
          ∃ c : (realConstantOpenPresheaf X).obj (Opposite.op V),
            (singularCochainMap ℝ ((Opens.toTopCat X).map (homOfLE hVU))).f 0 α =
              (realConstantOpenPresheafToSingularCochainZeroPresheaf X).app
                (Opposite.op V) c) ∧
      (∀ (x : X) (U : Opens X) (hxU : x ∈ U)
        (c : (realConstantOpenPresheaf X).obj (Opposite.op U)),
        ((realSingularCochainOpenPresheafComplex X).X 0).germ U x hxU
        ((realConstantOpenPresheafToSingularCochainZeroPresheaf X).app
              (Opposite.op U) c) = 0 →
          (realConstantOpenPresheaf X).germ U x hxU c = 0) :=
  ⟨standardRealConstantOpenPresheafToSingularCochainZeroPresheaf_comp_d X,
    standardRealConstantOpenPresheafToSingularCochainZeroPresheaf_scalar X,
    standardRealConstantOpenPresheafToSingularCochainZeroPresheaf_local_constant X,
    standardRealConstantOpenPresheafToSingularCochainZeroPresheaf_germ_eq_zero X⟩

private theorem realConstantOpenPresheafToSingularCochainZeroPresheaf_spec
    (X : TopCat.{v}) :
    ∃ _ :
        realConstantOpenPresheafToSingularCochainZeroPresheaf X ≫
          (realSingularCochainOpenPresheafComplex X).d 0 1 = 0,
      ∀ r : ℝ,
        realConstantOpenPresheafToSingularCochainZeroPresheaf X ≫
            (realSingularCochainOpenPresheafComplexScalarEnd X r).f 0 =
          realConstantOpenPresheafScalarEnd X r ≫
            realConstantOpenPresheafToSingularCochainZeroPresheaf X :=
  ⟨Classical.choose
      (realConstantOpenPresheafToSingularCochainZeroPresheaf_full_spec X),
    (Classical.choose_spec
      (realConstantOpenPresheafToSingularCochainZeroPresheaf_full_spec X)).1⟩
/--
%%handwave
name:
  Constant zero-cochains are closed
statement:
  For every space \(X\), the standard natural morphism
  \(\eta_X\colon\underline{\mathbb R}\to C^0(-;\mathbb R)\) satisfies
  \(d\circ\eta_X=0\).
proof:
  [The zero-cochain which has the constant value \(c\) on every singular vertex has vanishing coboundary.](lean:JJMath.Cohomology.standardRealConstantOpenPresheafToSingularCochainZeroPresheaf_comp_d)
-/
theorem realConstantOpenPresheafToSingularCochainZeroPresheaf_comp_d
    (X : TopCat.{v}) :
    realConstantOpenPresheafToSingularCochainZeroPresheaf X ≫
        (realSingularCochainOpenPresheafComplex X).d 0 1 = 0 :=
  Classical.choose (realConstantOpenPresheafToSingularCochainZeroPresheaf_spec X)
/--
%%handwave
name:
  Scalar naturality of the zero-cochain augmentation
statement:
  For every space \(X\) and \(r\in\mathbb R\), the standard morphism
  \(\eta_X\colon\underline{\mathbb R}\to C^0(-;\mathbb R)\) satisfies
  \(M_r\circ\eta_X=\eta_X\circ S_r\), where both endomorphisms are multiplication by
  \(r\).
proof:
  [Sending a constant to the zero-cochain with that value at every singular vertex commutes with multiplication by \(r\).](lean:JJMath.Cohomology.standardRealConstantOpenPresheafToSingularCochainZeroPresheaf_scalar)
-/
theorem realConstantOpenPresheafToSingularCochainZeroPresheaf_scalar
    (X : TopCat.{v}) (r : ℝ) :
    realConstantOpenPresheafToSingularCochainZeroPresheaf X ≫
        (realSingularCochainOpenPresheafComplexScalarEnd X r).f 0 =
      realConstantOpenPresheafScalarEnd X r ≫
        realConstantOpenPresheafToSingularCochainZeroPresheaf X :=
  (Classical.choose_spec
    (realConstantOpenPresheafToSingularCochainZeroPresheaf_spec X)) r

/--
%%handwave
name:
  Constants define sheafified singular zero-cochains
statement:
  Sheafifying the constant zero-cochain construction gives a morphism from
  the real constant sheaf to the sheaf of singular zero-cochains.
proof:
  Apply the sheafification functor to the natural transformation from the
  constant presheaf to singular zero-cochains on open subsets.
-/
noncomputable def realConstantAddSheafToSingularCochainSheafZero
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    RealConstantAddSheaf X ⟶ (realSingularCochainSheafComplex X).X 0 :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).map
    (realConstantOpenPresheafToSingularCochainZeroPresheaf X)

/--
%%handwave
name:
  Constants are closed sheafified singular zero-cochains
statement:
  The sheafified constant zero-cochain map is killed by the first singular
  coboundary.
proof:
  This is the sheafification of the presheaf-level identity saying that
  constant zero-cochains are closed.
-/
theorem realConstantAddSheafToSingularCochainSheafZero_comp_d
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    realConstantAddSheafToSingularCochainSheafZero X ≫
        (realSingularCochainSheafComplex X).d 0 1 = 0 := by
  let F := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}
  change
    F.map (realConstantOpenPresheafToSingularCochainZeroPresheaf X) ≫
        F.map ((realSingularCochainOpenPresheafComplex X).d 0 1) = 0
  calc
    F.map (realConstantOpenPresheafToSingularCochainZeroPresheaf X) ≫
        F.map ((realSingularCochainOpenPresheafComplex X).d 0 1)
        = F.map
            (realConstantOpenPresheafToSingularCochainZeroPresheaf X ≫
              (realSingularCochainOpenPresheafComplex X).d 0 1) := by
          exact (F.map_comp _ _).symm
    _ = F.map 0 := by
          exact congrArg F.map
            (realConstantOpenPresheafToSingularCochainZeroPresheaf_comp_d X)
    _ = 0 := by
          rw [F.map_zero]

/--
%%handwave
name:
  The sheafified constant zero-cochain map is scalar compatible
statement:
  The sheafified map from constants to singular zero-cochains commutes with
  multiplication by every real scalar.
proof:
  This is obtained by applying sheafification to the corresponding
  presheaf-level scalar-compatibility identity.
-/
theorem realConstantAddSheafToSingularCochainSheafZero_scalar
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (r : ℝ) :
    realConstantAddSheafToSingularCochainSheafZero X ≫
        (sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r).f 0 =
      realConstantSheafScalarEnd X r ≫
        realConstantAddSheafToSingularCochainSheafZero X := by
  let F := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}
  change
    F.map (realConstantOpenPresheafToSingularCochainZeroPresheaf X) ≫
        F.map ((realSingularCochainOpenPresheafComplexScalarEnd X r).f 0) =
      F.map (realConstantOpenPresheafScalarEnd X r) ≫
        F.map (realConstantOpenPresheafToSingularCochainZeroPresheaf X)
  calc
    F.map (realConstantOpenPresheafToSingularCochainZeroPresheaf X) ≫
        F.map ((realSingularCochainOpenPresheafComplexScalarEnd X r).f 0)
        = F.map
            (realConstantOpenPresheafToSingularCochainZeroPresheaf X ≫
              (realSingularCochainOpenPresheafComplexScalarEnd X r).f 0) := by
          exact (F.map_comp _ _).symm
    _ = F.map
          (realConstantOpenPresheafScalarEnd X r ≫
            realConstantOpenPresheafToSingularCochainZeroPresheaf X) := by
          exact congrArg F.map
            (realConstantOpenPresheafToSingularCochainZeroPresheaf_scalar X r)
    _ = F.map (realConstantOpenPresheafScalarEnd X r) ≫
        F.map (realConstantOpenPresheafToSingularCochainZeroPresheaf X) := by
          exact F.map_comp _ _

/--
%%handwave
name:
  Scalar action on real constant-sheaf cohomology
statement:
  A real scalar acts on real constant-sheaf cohomology by postcomposition with
  the corresponding scalar endomorphism of the coefficient sheaf.
proof:
  Represent sheaf cohomology as an Ext group and compose an Ext class with the
  degree-zero Ext class associated to scalar multiplication of the coefficient
  sheaf.
-/
noncomputable def realConstantSheafCohomologySMul (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) (r : ℝ) :
    RealConstantSheafCohomology X n → RealConstantSheafCohomology X n :=
  fun α =>
    CategoryTheory.Abelian.Ext.comp α
      (CategoryTheory.Abelian.Ext.mk₀ (realConstantSheafScalarEnd X r))
      (add_zero n)

@[simp]
theorem realConstantSheafCohomologySMul_one (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) (α : RealConstantSheafCohomology X n) :
    realConstantSheafCohomologySMul X n (1 : ℝ) α = α := by
  simp [realConstantSheafCohomologySMul]

@[simp]
theorem realConstantSheafCohomologySMul_zero_scalar (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) (α : RealConstantSheafCohomology X n) :
    realConstantSheafCohomologySMul X n (0 : ℝ) α = 0 := by
  simp [realConstantSheafCohomologySMul, realConstantSheafScalarEnd_zero]

@[simp]
theorem realConstantSheafCohomologySMul_zero (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) (r : ℝ) :
    realConstantSheafCohomologySMul X n r 0 = 0 := by
  rw [realConstantSheafCohomologySMul]
  exact CategoryTheory.Abelian.Ext.zero_comp (X := (constantSheaf
      (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)))
    (n := n)
    (CategoryTheory.Abelian.Ext.mk₀ (realConstantSheafScalarEnd X r)) n (add_zero n)

theorem realConstantSheafCohomologySMul_add (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) (r : ℝ) (α β : RealConstantSheafCohomology X n) :
    realConstantSheafCohomologySMul X n r (α + β) =
      realConstantSheafCohomologySMul X n r α +
        realConstantSheafCohomologySMul X n r β := by
  exact
    CategoryTheory.Abelian.Ext.add_comp α β
      (CategoryTheory.Abelian.Ext.mk₀ (realConstantSheafScalarEnd X r))
      (add_zero n)

theorem realConstantSheafCohomologySMul_add_scalar (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) (r s : ℝ) (α : RealConstantSheafCohomology X n) :
    realConstantSheafCohomologySMul X n (r + s) α =
      realConstantSheafCohomologySMul X n r α +
        realConstantSheafCohomologySMul X n s α := by
  simp [realConstantSheafCohomologySMul,
    realConstantSheafScalarEnd_add, CategoryTheory.Abelian.Ext.mk₀_add,
    CategoryTheory.Abelian.Ext.comp_add]

theorem realConstantSheafCohomologySMul_mul (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) (r s : ℝ) (α : RealConstantSheafCohomology X n) :
    realConstantSheafCohomologySMul X n (r * s) α =
      realConstantSheafCohomologySMul X n r
        (realConstantSheafCohomologySMul X n s α) := by
  simp only [realConstantSheafCohomologySMul, realConstantSheafScalarEnd_mul]
  rw [← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
  symm
  exact
    CategoryTheory.Abelian.Ext.comp_assoc
      α
      (CategoryTheory.Abelian.Ext.mk₀ (realConstantSheafScalarEnd X s))
      (CategoryTheory.Abelian.Ext.mk₀ (realConstantSheafScalarEnd X r))
      (add_zero n) (zero_add 0) (by simp)

/--
%%handwave
name:
  Real constant-sheaf cohomology is a real vector space
statement:
  Real constant-sheaf cohomology carries the real scalar multiplication
  induced by scalar endomorphisms of the constant real coefficient sheaf.
proof:
  The identity, composition, zero, addition, and distributivity laws follow
  from the corresponding laws for scalar endomorphisms and from bilinearity of
  Ext composition.
-/
noncomputable instance realConstantSheafCohomologyModule (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) :
    Module ℝ (RealConstantSheafCohomology X n) where
  smul r α := realConstantSheafCohomologySMul X n r α
  one_smul α := realConstantSheafCohomologySMul_one X n α
  mul_smul r s α := realConstantSheafCohomologySMul_mul X n r s α
  smul_zero r := realConstantSheafCohomologySMul_zero X n r
  smul_add r α β := realConstantSheafCohomologySMul_add X n r α β
  zero_smul α := realConstantSheafCohomologySMul_zero_scalar X n α
  add_smul r s α := realConstantSheafCohomologySMul_add_scalar X n r s α
/--
%%handwave
name:
  Formula for scalar multiplication on constant-sheaf cohomology
statement:
  For \(r\in\mathbb R\) and
  \(\alpha\in H^n(X;\underline{\mathbb R})\), the module product
  \(r\alpha\) is the postcomposition action of the coefficient-sheaf
  endomorphism given by multiplication by \(r\).
proof:
  This is the defining scalar multiplication of the real module structure on
  \(H^n(X;\underline{\mathbb R})\).
-/
@[simp]
theorem realConstantSheafCohomology_smul_eq (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) (r : ℝ) (α : RealConstantSheafCohomology X n) :
    r • α = realConstantSheafCohomologySMul X n r α :=
  rfl

/--
%%handwave
name:
  Augmented singular cochain sheaf complex data
statement:
  The raw singular-cochain construction supplies a cochain complex of sheaves,
  an augmentation from the real constant sheaf, scalar endomorphisms extending
  scalar multiplication on constants, and scalar-compatible identifications
  of its global-section cohomology with ordinary real singular cohomology.
proof:
  This is a packaging definition for the constructive part of the singular
  cochain sheaf resolution.
-/
structure RealSingularCochainSheafAugmentedComplexData
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] where
  K :
    CochainComplex
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}) ℕ
  ε : RealConstantAddSheaf X ⟶ K.X 0
  hε : ε ≫ K.d 0 1 = 0
  scalarEnd : ℝ → (K ⟶ K)
  scalar_augmentation :
    ∀ r : ℝ, ε ≫ (scalarEnd r).f 0 = realConstantSheafScalarEnd X r ≫ ε
  globalComparison :
    ∀ n : ℕ,
      ∃ e :
        ↥((((Sheaf.Γ (Opens.grothendieckTopology X)
            AddCommGrpCat.{v}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K).homology n) ≃+
          RealSingularCohomology X n,
        ∀ (r : ℝ)
          (x :
            ↥((((Sheaf.Γ (Opens.grothendieckTopology X)
                AddCommGrpCat.{v}).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj K).homology n)),
          e ((HomologicalComplex.homologyMap
                (((Sheaf.Γ (Opens.grothendieckTopology X)
                  AddCommGrpCat.{v}).mapHomologicalComplex
                  (ComplexShape.up ℕ)).map (scalarEnd r)) n) x) =
            r • e x

/--
%%handwave
name:
  Singular cochain sheaf resolution data
statement:
  The data of the singular-cochain resolution of the real constant sheaf on
  a space \(X\) consists of a cochain complex of sheaves, an augmentation from
  the constant real sheaf, exactness of the augmented complex, acyclicity of
  each term, scalar endomorphisms extending scalar multiplication on the
  constant sheaf, and scalar-compatible identifications of global-section
  cohomology with ordinary real singular cohomology.
proof:
  This is a packaging definition.  The mathematical content is supplied by
  the existence theorem for paracompact locally contractible spaces.
-/
structure RealSingularCochainSheafResolutionData
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] where
  K :
    CochainComplex
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}) ℕ
  ε : RealConstantAddSheaf X ⟶ K.X 0
  hε : ε ≫ K.d 0 1 = 0
  exact_zero :
    ({ f := ε, g := K.d 0 1, zero := hε } :
      ShortComplex
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})).Exact
  mono_ε : Mono ε
  exact_pos : ∀ m : ℕ, K.ExactAt (m + 1)
  acyclic : ∀ p q : ℕ, 0 < q → Subsingleton ((K.X p).H q)
  scalarEnd : ℝ → (K ⟶ K)
  scalar_augmentation :
    ∀ r : ℝ, ε ≫ (scalarEnd r).f 0 = realConstantSheafScalarEnd X r ≫ ε
  globalComparison :
    ∀ n : ℕ,
      ∃ e :
        ↥((((Sheaf.Γ (Opens.grothendieckTopology X)
            AddCommGrpCat.{v}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K).homology n) ≃+
          RealSingularCohomology X n,
        ∀ (r : ℝ)
          (x :
            ↥((((Sheaf.Γ (Opens.grothendieckTopology X)
                AddCommGrpCat.{v}).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj K).homology n)),
          e ((HomologicalComplex.homologyMap
                (((Sheaf.Γ (Opens.grothendieckTopology X)
                  AddCommGrpCat.{v}).mapHomologicalComplex
                  (ComplexShape.up ℕ)).map (scalarEnd r)) n) x) =
            r • e x

/--
%%handwave
name:
  Augmentation data for the sheafified open singular-cochain complex
statement:
  The standard augmentation data consists of a morphism from the constant real
  sheaf to degree-zero singular cochains, proof that the first coboundary
  kills it, and compatibility with scalar multiplication.
proof:
  This packages the constructive part of the augmentation before the
  stalkwise exactness proof.
-/
structure SheafifiedOpenRealSingularCochainSheafAugmentationData
    (X : TopCat.{v})
    [ParacompactSpace X]
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (hloc : LocallyContractibleSpace X) where
  ε : RealConstantAddSheaf X ⟶ (realSingularCochainSheafComplex X).X 0
  hε : ε ≫ (realSingularCochainSheafComplex X).d 0 1 = 0
  scalar_augmentation :
    ∀ r : ℝ,
      ε ≫
          (sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r).f 0 =
        realConstantSheafScalarEnd X r ≫ ε

/--
%%handwave
name:
  The standard sheafified singular-cochain augmentation
statement:
  The sheafification of the constant zero-cochain construction gives the
  standard augmentation data for the sheafified open singular-cochain complex.
proof:
  Use the sheafified map from constants to singular zero-cochains, the fact
  that constant zero-cochains are closed, and scalar compatibility of the
  sheafified construction.
-/
noncomputable def sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] :
    SheafifiedOpenRealSingularCochainSheafAugmentationData X hloc where
  ε := realConstantAddSheafToSingularCochainSheafZero X
  hε := realConstantAddSheafToSingularCochainSheafZero_comp_d X
  scalar_augmentation :=
    realConstantAddSheafToSingularCochainSheafZero_scalar X

/--
%%handwave
name:
  The degree-zero short complex of an augmented singular-cochain sheaf complex
statement:
  An augmentation of the sheafified open singular-cochain complex determines
  a short complex consisting of the constant real sheaf, degree-zero
  singular cochains, and degree-one singular cochains.
proof:
  The defining condition on the augmentation says exactly that the composite
  through the first coboundary is zero.
-/
abbrev sheafifiedOpenRealSingularCochainSheafAugmentationShortComplex
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (A : SheafifiedOpenRealSingularCochainSheafAugmentationData X hloc) :
    ShortComplex
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}) :=
  { f := A.ε
    g := (realSingularCochainSheafComplex X).d 0 1
    zero := A.hε }

instance sheafForget_stalkFunctor_preservesZeroMorphisms
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (x : X) :
    (TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).PreservesZeroMorphisms := by
  haveI :
      (TopCat.Sheaf.forget AddCommGrpCat.{v} X).Additive := inferInstance
  haveI :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).Additive := inferInstance
  infer_instance

/-- The stalk of the augmented degree-zero singular-cochain short complex. -/
abbrev sheafifiedOpenRealSingularCochainSheafAugmentationStalkShortComplex
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (A : SheafifiedOpenRealSingularCochainSheafAugmentationData X hloc)
    (x : X) :
    ShortComplex AddCommGrpCat.{v} :=
  @ShortComplex.map _ _ _ _ _ _
    (sheafifiedOpenRealSingularCochainSheafAugmentationShortComplex
      (X := X) hloc A)
    (TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x)
    (sheafForget_stalkFunctor_preservesZeroMorphisms X x)

/--
%%handwave
name:
  The presheaf degree-zero augmented singular-cochain short complex
statement:
  Before sheafification, the constant real presheaf, singular zero-cochains,
  and singular one-cochains form a short complex on open subsets.
proof:
  The augmentation is the constant zero-cochain map, and constant
  zero-cochains have zero singular coboundary.
-/
abbrev realSingularCochainOpenPresheafAugmentationShortComplex
    (X : TopCat.{v}) :
    ShortComplex (TopCat.Presheaf AddCommGrpCat.{v} X) :=
  { f := realConstantOpenPresheafToSingularCochainZeroPresheaf X
    g := (realSingularCochainOpenPresheafComplex X).d 0 1
    zero := realConstantOpenPresheafToSingularCochainZeroPresheaf_comp_d X }

/--
%%handwave
name:
  The stalk of the presheaf degree-zero augmented singular-cochain complex
statement:
  Taking the stalk at a point turns the presheaf degree-zero augmented
  singular-cochain short complex into a short complex of abelian groups.
proof:
  Apply the ordinary stalk functor to the presheaf short complex.
-/
abbrev realSingularCochainOpenPresheafAugmentationStalkShortComplex
    (X : TopCat.{v}) (x : X) :
    ShortComplex AddCommGrpCat.{v} :=
  @ShortComplex.map _ _ _ _ _ _
    (realSingularCochainOpenPresheafAugmentationShortComplex X)
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x)
    (by infer_instance)

/-- The stalk of a positive-degree singular-cochain sheaf short complex. -/
abbrev realSingularCochainSheafComplexStalkShortComplex
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (m : ℕ) (x : X) :
    ShortComplex AddCommGrpCat.{v} :=
  @ShortComplex.map _ _ _ _ _ _
    ((realSingularCochainSheafComplex X).sc (m + 1))
    (TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x)
    (sheafForget_stalkFunctor_preservesZeroMorphisms X x)

/-- The stalk of a positive-degree open singular-cochain presheaf short complex. -/
abbrev realSingularCochainOpenPresheafComplexStalkShortComplex
    (X : TopCat.{v}) (m : ℕ) (x : X) :
    ShortComplex AddCommGrpCat.{v} :=
  @ShortComplex.map _ _ _ _ _ _
    ((realSingularCochainOpenPresheafComplex X).sc' m (m + 1) (m + 2))
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x)
    (by infer_instance)

/--
%%handwave
name:
  A cycle with zero homology class is a boundary
statement:
  In a short complex of modules, if a cycle represents the zero homology
  class, then it is the image of an element in the previous term.
proof:
  Use the concrete quotient model of homology of a short complex of modules.
  The homology class is the quotient of the cycle module by the image of the
  previous map; being zero in that quotient means precisely that the cycle
  lies in this image.
-/
theorem shortComplex_moduleCat_exists_preimage_of_homologyπ_eq_zero
    (R : Type u) [Ring R]
    (S : ShortComplex (ModuleCat.{v} R))
    (x₂ : S.X₂) (hx₂ : S.g x₂ = 0)
    (hclass : S.homologyπ (S.cyclesMk x₂ hx₂) = 0) :
    ∃ x₁ : S.X₁, S.f x₁ = x₂ := by
  have hclass' :
      (ConcreteCategory.hom S.moduleCatHomologyIso.hom)
        ((ConcreteCategory.hom S.homologyπ) (S.cyclesMk x₂ hx₂)) = 0 := by
    exact
      (congrArg (fun y => (ConcreteCategory.hom S.moduleCatHomologyIso.hom) y)
        hclass).trans S.moduleCatHomologyIso.hom.hom.map_zero
  have hπ := ShortComplex.π_moduleCatCyclesIso_hom_apply S (S.cyclesMk x₂ hx₂)
  have hq :
      S.moduleCatToCycles.range.mkQ
        ((ConcreteCategory.hom S.moduleCatCyclesIso.hom) (S.cyclesMk x₂ hx₂)) = 0 := by
    exact hπ.symm.trans hclass'
  have hmem :
      S.moduleCatCyclesIso.hom (S.cyclesMk x₂ hx₂) ∈
        LinearMap.range S.moduleCatToCycles := by
    simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hq
  rcases hmem with ⟨x₁, hx₁⟩
  refine ⟨x₁, ?_⟩
  have hsub :
      S.moduleCatLeftHomologyData.i
          (S.moduleCatCyclesIso.hom (S.cyclesMk x₂ hx₂)) = S.f x₁ := by
    exact congrArg (fun z => S.moduleCatLeftHomologyData.i z) hx₁.symm
  have hleft :
      S.moduleCatLeftHomologyData.i
          (S.moduleCatCyclesIso.hom (S.cyclesMk x₂ hx₂)) = x₂ := by
    simpa [ShortComplex.moduleCatLeftHomologyData_i_hom] using
      (ShortComplex.moduleCatCyclesIso_hom_i_apply S (S.cyclesMk x₂ hx₂)).trans
        (ShortComplex.i_cyclesMk S x₂ hx₂)
  exact hsub.symm.trans hleft

/--
%%handwave
name:
  A cycle with zero abelian-group homology class is a boundary
statement:
  In a short complex of abelian groups, if a cycle represents the zero
  homology class, then it is the image of an element in the previous term.
proof:
  Use the concrete quotient model of homology of a short complex of abelian
  groups.  The homology class is the quotient of the cycle group by the image
  of the previous map; being zero in that quotient means precisely that the
  cycle lies in this image.
-/
theorem shortComplex_addCommGrp_exists_preimage_of_homologyπ_eq_zero
    (S : ShortComplex Ab.{v})
    (x₂ : S.X₂) (hx₂ : S.g x₂ = 0)
    (hclass : S.homologyπ (S.abCyclesIso.inv ⟨x₂, hx₂⟩) = 0) :
    ∃ x₁ : S.X₁, S.f x₁ = x₂ := by
  let z : S.cycles := S.abCyclesIso.inv ⟨x₂, hx₂⟩
  have hclass' :
      (ConcreteCategory.hom S.abHomologyIso.hom)
        ((ConcreteCategory.hom S.homologyπ) z) = 0 := by
    exact
      (congrArg (fun y => (ConcreteCategory.hom S.abHomologyIso.hom) y)
        hclass).trans S.abHomologyIso.hom.hom.map_zero
  have hπ :
      (ConcreteCategory.hom S.abHomologyIso.hom)
        ((ConcreteCategory.hom S.homologyπ) z) =
      QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles) ⟨x₂, hx₂⟩ := by
    have hπ_morph :
        S.homologyπ ≫ S.abHomologyIso.hom =
          S.abCyclesIso.hom ≫ S.abLeftHomologyData.π :=
      S.abLeftHomologyData.homologyπ_comp_homologyIso_hom
    simpa [z, ShortComplex.abLeftHomologyData] using
      congrArg (fun f => (ConcreteCategory.hom f) z) hπ_morph
  have hq :
      QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
        ⟨x₂, hx₂⟩ = 0 := by
    exact hπ.symm.trans hclass'
  have hmem :
      (⟨x₂, hx₂⟩ : AddMonoidHom.ker S.g.hom) ∈ AddMonoidHom.range S.abToCycles := by
    simpa [QuotientAddGroup.eq_zero_iff] using hq
  rcases hmem with ⟨x₁, hx₁⟩
  refine ⟨x₁, ?_⟩
  simpa only [Subtype.ext_iff, ShortComplex.abToCycles_apply_coe] using hx₁

/--
%%handwave
name:
  A zero abelian-group homology class has a primitive
statement:
  In a short complex of abelian groups, if a cycle represents zero in
  homology, then its underlying element is the image of an element in the
  previous term.
proof:
  Identify the cycle with its concrete kernel representative and apply
  [a cycle with zero abelian-group homology class is a boundary](lean:JJMath.Cohomology.shortComplex_addCommGrp_exists_preimage_of_homologyπ_eq_zero).
-/
theorem shortComplex_addCommGrp_exists_preimage_iCycles_of_homologyπ_eq_zero
    (S : ShortComplex Ab.{v})
    (z : S.cycles)
    (hclass : S.homologyπ z = 0) :
    ∃ x₁ : S.X₁, S.f x₁ = S.iCycles z := by
  let x₂ : S.X₂ := S.iCycles z
  have hx₂ : S.g x₂ = 0 := by
    change S.g (S.iCycles z) = 0
    rw [← ConcreteCategory.comp_apply, S.iCycles_g]
    rfl
  have hz :
      S.abCyclesIso.inv ⟨x₂, hx₂⟩ = z := by
    apply (AddCommGrpCat.mono_iff_injective S.iCycles).1 inferInstance
    simpa [x₂] using S.abCyclesIso_inv_apply_iCycles ⟨x₂, hx₂⟩
  exact
    shortComplex_addCommGrp_exists_preimage_of_homologyπ_eq_zero
      S x₂ hx₂ (by simpa [hz] using hclass)

/--
%%handwave
name:
  A zero positive cohomology class in an abelian cochain complex has a primitive
statement:
  In a cochain complex of abelian groups, a closed \((m+1)\)-cochain whose
  cohomology class is zero is the coboundary of an \(m\)-cochain.
proof:
  Apply [a zero abelian-group homology class has a primitive](lean:JJMath.Cohomology.shortComplex_addCommGrp_exists_preimage_iCycles_of_homologyπ_eq_zero) to the short complex centered in degree \(m+1\), then identify the previous object with degree \(m\).
-/
theorem cochainComplex_addCommGrp_exists_preimage_of_homologyπ_eq_zero
    {K : CochainComplex Ab.{v} ℕ}
    (m : ℕ)
    (z : K.cycles (m + 1))
    (hclass : K.homologyπ (m + 1) z = 0) :
    ∃ β : K.X m, K.d m (m + 1) β = K.iCycles (m + 1) z := by
  have hprev : (ComplexShape.up ℕ).prev (m + 1) = m := by
    exact (ComplexShape.up ℕ).prev_eq' (by simp [ComplexShape.up_Rel])
  let S : ShortComplex Ab.{v} := K.sc (m + 1)
  have hclassS : S.homologyπ z = 0 := by
    simpa [S] using hclass
  rcases shortComplex_addCommGrp_exists_preimage_iCycles_of_homologyπ_eq_zero
      S z hclassS with
    ⟨β, hβ⟩
  let β' : K.X m := (K.XIsoOfEq hprev).hom β
  refine ⟨β', ?_⟩
  change
    (ConcreteCategory.hom (K.d m (m + 1)))
        ((ConcreteCategory.hom (K.XIsoOfEq hprev).hom) β) =
      (ConcreteCategory.hom (K.iCycles (m + 1))) z
  rw [← ConcreteCategory.comp_apply, K.XIsoOfEq_hom_comp_d hprev (m + 1)]
  simpa [S] using hβ

/--
%%handwave
name:
  An explicit positive-degree coboundary has zero cohomology class
statement:
  In a cochain complex of abelian groups, if a closed \((m+1)\)-cochain is
  the coboundary of an \(m\)-cochain, then its cohomology class is zero.
proof:
  The differential factors through the cycle object by the canonical map
  \(C^m\to Z^{m+1}\), and the homology-class map kills this image.
-/
theorem cochainComplex_addCommGrp_homologyπ_eq_zero_of_preimage
    {K : CochainComplex Ab.{v} ℕ}
    (m : ℕ)
    (z : K.cycles (m + 1))
    (β : K.X m)
    (hβ : K.d m (m + 1) β = K.iCycles (m + 1) z) :
    K.homologyπ (m + 1) z = 0 := by
  have hz :
      (K.toCycles m (m + 1)) β = z := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles (m + 1))).1 inferInstance
    change
      (ConcreteCategory.hom (K.iCycles (m + 1)))
          ((ConcreteCategory.hom (K.toCycles m (m + 1))) β) =
        (ConcreteCategory.hom (K.iCycles (m + 1))) z
    rw [← ConcreteCategory.comp_apply, K.toCycles_i]
    exact hβ
  rw [← hz]
  change
    (ConcreteCategory.hom (K.toCycles m (m + 1) ≫
      K.homologyπ (m + 1))) β = 0
  rw [K.toCycles_comp_homologyπ]
  rfl

/--
%%handwave
name:
  A cochain map which is zero on cohomology sends closed abelian cochains to boundaries
statement:
  Let \(f:K^\bullet\to L^\bullet\) be a cochain map of abelian groups.  If
  the induced map on cohomology in degree \(m+1\) is zero, then the image of
  every closed \((m+1)\)-cochain is a coboundary in \(L^\bullet\).
proof:
  Represent the closed cochain as a cycle and use naturality of the homology
  class map.  Since the induced map on homology is zero, the image cycle has
  zero homology class.  Apply the abelian-group primitive criterion for a
  zero cohomology class.
-/
theorem cochainMap_addCommGrp_lift_closed_of_homologyMap_zero
    {K L : CochainComplex Ab.{v} ℕ} (φ : K ⟶ L)
    (m : ℕ)
    (hφ : HomologicalComplex.homologyMap φ (m + 1) = 0)
    (α : K.X (m + 1))
    (hα : K.d (m + 1) (m + 2) α = 0) :
    ∃ β : L.X m, L.d m (m + 1) β = φ.f (m + 1) α := by
  have hnext : (ComplexShape.up ℕ).next (m + 1) = m + 2 := by
    exact (ComplexShape.up ℕ).next_eq' (by simp [ComplexShape.up_Rel])
  have hαS : (K.sc (m + 1)).g α = 0 := by
    change
      (ConcreteCategory.hom
        (K.d (m + 1) ((ComplexShape.up ℕ).next (m + 1)))) α = 0
    rw [hnext]
    exact hα
  let xK : AddMonoidHom.ker (K.sc (m + 1)).g.hom := ⟨α, hαS⟩
  let zK : K.cycles (m + 1) := (K.sc (m + 1)).abCyclesIso.inv xK
  have hclosedImage :
      L.d (m + 1) (m + 2) (φ.f (m + 1) α) = 0 := by
    have hcomm := φ.comm (m + 1) (m + 2)
    change
      (ConcreteCategory.hom (L.d (m + 1) (m + 2)))
        ((ConcreteCategory.hom (φ.f (m + 1))) α) = 0
    rw [← ConcreteCategory.comp_apply, hcomm, ConcreteCategory.comp_apply, hα]
    exact (φ.f (m + 2)).hom.map_zero
  have hclosedImageS : (L.sc (m + 1)).g (φ.f (m + 1) α) = 0 := by
    change
      (ConcreteCategory.hom
        (L.d (m + 1) ((ComplexShape.up ℕ).next (m + 1))))
          ((ConcreteCategory.hom (φ.f (m + 1))) α) = 0
    rw [hnext]
    exact hclosedImage
  let xL : AddMonoidHom.ker (L.sc (m + 1)).g.hom :=
    ⟨φ.f (m + 1) α, hclosedImageS⟩
  let zL : L.cycles (m + 1) := (L.sc (m + 1)).abCyclesIso.inv xL
  have hzeroMap :
      (HomologicalComplex.homologyMap φ (m + 1))
        ((K.homologyπ (m + 1)) zK) = 0 := by
    rw [hφ]
    rfl
  have hnat :=
    congrArg (fun f => (ConcreteCategory.hom f) zK)
      (HomologicalComplex.homologyπ_naturality φ (m + 1))
  have hclass_cyclesMap :
      (L.homologyπ (m + 1)) ((HomologicalComplex.cyclesMap φ (m + 1)) zK) = 0 := by
    exact hnat.symm.trans hzeroMap
  have hz_eq :
      (HomologicalComplex.cyclesMap φ (m + 1)) zK = zL := by
    apply (AddCommGrpCat.mono_iff_injective (L.iCycles (m + 1))).1 inferInstance
    have hleft :
        (L.iCycles (m + 1)) ((HomologicalComplex.cyclesMap φ (m + 1)) zK) =
          (φ.f (m + 1)) ((K.iCycles (m + 1)) zK) := by
      change
        (ConcreteCategory.hom (HomologicalComplex.cyclesMap φ (m + 1) ≫
          L.iCycles (m + 1))) zK =
        (ConcreteCategory.hom (K.iCycles (m + 1) ≫ φ.f (m + 1))) zK
      rw [HomologicalComplex.cyclesMap_i]
    have hzK_i : (K.iCycles (m + 1)) zK = α := by
      simpa [zK, xK] using
        ShortComplex.abCyclesIso_inv_apply_iCycles (K.sc (m + 1)) xK
    have hzL_i : (L.iCycles (m + 1)) zL = φ.f (m + 1) α := by
      simpa [zL, xL] using
        ShortComplex.abCyclesIso_inv_apply_iCycles (L.sc (m + 1)) xL
    calc
      (L.iCycles (m + 1)) ((HomologicalComplex.cyclesMap φ (m + 1)) zK)
          = (φ.f (m + 1)) ((K.iCycles (m + 1)) zK) := hleft
      _ = φ.f (m + 1) α := by rw [hzK_i]
      _ = (L.iCycles (m + 1)) zL := hzL_i.symm
  have hclassL : L.homologyπ (m + 1) zL = 0 := by
    simpa [hz_eq] using hclass_cyclesMap
  rcases cochainComplex_addCommGrp_exists_preimage_of_homologyπ_eq_zero
      (K := L) m zL hclassL with
    ⟨β, hβ⟩
  refine ⟨β, ?_⟩
  have hzL_i : (L.iCycles (m + 1)) zL = φ.f (m + 1) α := by
    simpa [zL, xL] using
      ShortComplex.abCyclesIso_inv_apply_iCycles (L.sc (m + 1)) xL
  exact hβ.trans hzL_i

/--
%%handwave
name:
  A zero degree-zero cohomology class in an abelian cochain complex is zero as a cycle
statement:
  In a cochain complex of abelian groups indexed by the natural numbers, a
  degree-zero cycle whose cohomology class is zero is itself zero.
proof:
  The quotient map from degree-zero cycles to degree-zero cohomology is an
  isomorphism, since there is no incoming differential in degree zero.
-/
theorem cochainComplex_addCommGrp_cycle_zero_of_homologyπ_zero_eq_zero
    {K : CochainComplex Ab.{v} ℕ}
    (z : K.cycles 0)
    (hclass : K.homologyπ 0 z = 0) :
    z = 0 := by
  apply (AddCommGrpCat.mono_iff_injective (K.homologyπ 0)).1 inferInstance
  simpa using hclass

/--
%%handwave
name:
  A cochain map which is zero on cohomology sends closed cochains to boundaries
statement:
  Let \(f:K^\bullet\to L^\bullet\) be a cochain map of module complexes.  If
  the induced map on cohomology in degree \(m+1\) is zero, then the image of
  every closed \((m+1)\)-cochain is a coboundary in \(L^\bullet\).
proof:
  Represent the closed cochain as a cycle and use naturality of the homology
  class map.  Since the induced map on homology is zero, the image cycle has
  zero homology class.  Apply [a cycle with zero homology class is a boundary](lean:JJMath.Cohomology.shortComplex_moduleCat_exists_preimage_of_homologyπ_eq_zero) to the short complex centered in degree \(m+1\).
-/
theorem cochainMap_lift_closed_of_homologyMap_zero
    (R : Type u) [Ring R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ L)
    (m : ℕ)
    (hφ : HomologicalComplex.homologyMap φ (m + 1) = 0)
    (α : K.X (m + 1))
    (hα : K.d (m + 1) (m + 2) α = 0) :
    ∃ β : L.X m, L.d m (m + 1) β = φ.f (m + 1) α := by
  have hnext : (ComplexShape.up ℕ).next (m + 1) = m + 2 := by
    exact (ComplexShape.up ℕ).next_eq' (by simp [ComplexShape.up_Rel])
  have hprev : (ComplexShape.up ℕ).prev (m + 1) = m := by
    exact (ComplexShape.up ℕ).prev_eq' (by simp [ComplexShape.up_Rel])
  let zK : K.cycles (m + 1) := K.cyclesMk α (m + 2) hnext hα
  have hclosedImage :
      L.d (m + 1) (m + 2) (φ.f (m + 1) α) = 0 := by
    have hcomm := φ.comm (m + 1) (m + 2)
    change
      (ConcreteCategory.hom (L.d (m + 1) (m + 2)))
        ((ConcreteCategory.hom (φ.f (m + 1))) α) = 0
    rw [← ConcreteCategory.comp_apply, hcomm, ConcreteCategory.comp_apply, hα]
    exact (φ.f (m + 2)).hom.map_zero
  let S : ShortComplex (ModuleCat.{v} R) := L.sc (m + 1)
  have hclosedS : S.g (φ.f (m + 1) α) = 0 := by
    change
      (ConcreteCategory.hom (L.d (m + 1) ((ComplexShape.up ℕ).next (m + 1))))
        ((ConcreteCategory.hom (φ.f (m + 1))) α) = 0
    rw [hnext]
    exact hclosedImage
  let zL : L.cycles (m + 1) :=
    S.cyclesMk (φ.f (m + 1) α) hclosedS
  have hzeroMap :
      (HomologicalComplex.homologyMap φ (m + 1))
        ((K.homologyπ (m + 1)) zK) = 0 := by
    rw [hφ]
    rfl
  have hnat :=
    congrArg (fun f => (ConcreteCategory.hom f) zK)
      (HomologicalComplex.homologyπ_naturality φ (m + 1))
  have hclass_cyclesMap :
      (L.homologyπ (m + 1)) ((HomologicalComplex.cyclesMap φ (m + 1)) zK) = 0 := by
    exact hnat.symm.trans hzeroMap
  have hz_eq :
      (HomologicalComplex.cyclesMap φ (m + 1)) zK = zL := by
    apply (ModuleCat.mono_iff_injective (L.iCycles (m + 1))).1 inferInstance
    have hleft :
        (L.iCycles (m + 1)) ((HomologicalComplex.cyclesMap φ (m + 1)) zK) =
          (φ.f (m + 1)) ((K.iCycles (m + 1)) zK) := by
      change
        (ConcreteCategory.hom (HomologicalComplex.cyclesMap φ (m + 1) ≫
          L.iCycles (m + 1))) zK =
        (ConcreteCategory.hom (K.iCycles (m + 1) ≫ φ.f (m + 1))) zK
      rw [HomologicalComplex.cyclesMap_i]
    have hzK_i : (K.iCycles (m + 1)) zK = α := by
      simpa [zK] using HomologicalComplex.i_cyclesMk K α (m + 2) hnext hα
    have hzL_i : (L.iCycles (m + 1)) zL = φ.f (m + 1) α := by
      simpa [zL, S] using ShortComplex.i_cyclesMk S (φ.f (m + 1) α) hclosedS
    calc
      (L.iCycles (m + 1)) ((HomologicalComplex.cyclesMap φ (m + 1)) zK)
          = (φ.f (m + 1)) ((K.iCycles (m + 1)) zK) := hleft
      _ = φ.f (m + 1) α := by rw [hzK_i]
      _ = (L.iCycles (m + 1)) zL := hzL_i.symm
  have hclassS :
      S.homologyπ (S.cyclesMk (φ.f (m + 1) α) hclosedS) = 0 := by
    simpa [zL, S, hz_eq] using hclass_cyclesMap
  rcases shortComplex_moduleCat_exists_preimage_of_homologyπ_eq_zero R S
      (φ.f (m + 1) α) hclosedS hclassS with
    ⟨β, hβ⟩
  let β' : L.X m := (L.XIsoOfEq hprev).hom β
  refine ⟨β', ?_⟩
  change
    (ConcreteCategory.hom (L.d m (m + 1)))
        ((ConcreteCategory.hom (L.XIsoOfEq hprev).hom) β) =
      (ConcreteCategory.hom (φ.f (m + 1))) α
  rw [← ConcreteCategory.comp_apply, L.XIsoOfEq_hom_comp_d hprev (m + 1)]
  simpa [S] using hβ

private theorem singularCohomologyMap_eq_of_homotopy_on_homologyMap
    (R : Type u) [CommRing R] {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (n : ℕ) :
    HomologicalComplex.homologyMap (singularCochainMap R f) n =
      HomologicalComplex.homologyMap (singularCochainMap R g) n := by
  rcases singularCochainMap_homotopy_of_chainHomotopy_for_singularCohomology R
      (H.singularChainComplexFunctorObjMap
        (SingularCohomologyCoefficient.{u, v} R)) with
    ⟨h⟩
  exact h.homologyMap_eq n

private theorem linearYonedaObj_single₀_positive_isZero
    (R : Type u) [CommRing R]
    (A : ModuleCat.{max u v} R)
    (m : ℕ) :
    IsZero ((((ChainComplex.single₀ (ModuleCat.{max u v} R)).obj A).linearYonedaObj R
      (SingularCohomologyCoefficient.{u, v} R)).homology (m + 1)) := by
  let F := (((linearYoneda R (ModuleCat.{max u v} R)).obj
      (SingularCohomologyCoefficient.{u, v} R)).rightOp)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  change (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((ChainComplex.single₀ (ModuleCat.{max u v} R)).obj A)).unop).ExactAt (m + 1)
  apply HomologicalComplex.ExactAt.unop
  let e := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).app A
  exact
    (ChainComplex.exactAt_succ_single_obj (C := (ModuleCat.{max u v} R)ᵒᵖ)
      (F.obj A) m).of_iso e.symm

private theorem linearYonedaObj_alternatingConst_positive_isZero
    (R : Type u) [CommRing R]
    (A : ModuleCat.{max u v} R)
    (m : ℕ) :
    IsZero (((ChainComplex.alternatingConst.obj A).linearYonedaObj R
      (SingularCohomologyCoefficient.{u, v} R)).homology (m + 1)) := by
  let F := (((linearYoneda R (ModuleCat.{max u v} R)).obj
      (SingularCohomologyCoefficient.{u, v} R)).rightOp)
  let K : ChainComplex (ModuleCat.{max u v} R) ℕ := ChainComplex.alternatingConst.obj A
  let L : ChainComplex (ModuleCat.{max u v} R) ℕ :=
    (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj A
  have hsingle :
      IsZero ((((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L).unop).homology
        (m + 1)) := by
    simpa [L] using linearYonedaObj_single₀_positive_isZero (R := R) (A := A) (m := m)
  let eChain : HomotopyEquiv K L := ChainComplex.alternatingConstHomotopyEquiv A
  let eOpp : HomotopyEquiv ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K)
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L) :=
    F.mapHomotopyEquiv eChain
  let eHom := eOpp.toHomologyIso (m + 1)
  let eUnopHom :
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).unop).homology (m + 1) ≅
        (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L).unop).homology (m + 1) :=
    HomologicalComplex.homologyUnop
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) (m + 1) ≪≫
      eHom.symm.unop ≪≫
      (HomologicalComplex.homologyUnop
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L) (m + 1)).symm
  change IsZero ((((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).unop).homology
    (m + 1))
  exact hsingle.of_iso eUnopHom

/--
%%handwave
name:
  A point has no positive singular cohomology
statement:
  For every commutative coefficient ring \(R\), the singular cohomology of a
  one-point space vanishes in degree \(m+1\).
proof:
  The singular chain complex of a one-point space is the alternating constant
  complex, which is homotopy equivalent to the complex concentrated in degree
  zero.  Dualizing the homotopy equivalence gives a cochain complex whose
  positive cohomology is zero.
-/
theorem singularCohomology_point_positive_isZero
    (R : Type u) [CommRing R] (m : ℕ) :
    IsZero (SingularCohomology R (TopCat.of PUnit.{v+1}) (m + 1)) := by
  let F := (((linearYoneda R (ModuleCat.{max u v} R)).obj
      (SingularCohomologyCoefficient.{u, v} R)).rightOp)
  let K : ChainComplex (ModuleCat.{max u v} R) ℕ :=
    SingularChains R (TopCat.of PUnit.{v+1})
  let A : ModuleCat.{max u v} R :=
    ∐ fun _ : TopCat.of PUnit.{v+1} ↦ SingularCohomologyCoefficient.{u, v} R
  let L : ChainComplex (ModuleCat.{max u v} R) ℕ := ChainComplex.alternatingConst.obj A
  let e : K ≅ L :=
    AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
      (C := ModuleCat.{max u v} R) (R := SingularCohomologyCoefficient.{u, v} R)
      (X := TopCat.of PUnit.{v+1})
  have hL :
      IsZero ((((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L).unop).homology
        (m + 1)) := by
    simpa [L] using
      linearYonedaObj_alternatingConst_positive_isZero (R := R) (A := A) (m := m)
  let eDual : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L).unop ≅
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).unop :=
    (HomologicalComplex.unopFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).mapIso
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).mapIso e).op)
  have hExactL :
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L).unop).ExactAt (m + 1) := by
    simpa [← HomologicalComplex.exactAt_iff_isZero_homology] using hL
  have hExactK :
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).unop).ExactAt (m + 1) :=
    hExactL.of_iso eDual
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  change (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).unop).ExactAt (m + 1)
  exact hExactK

private theorem singularCohomologyMap_eq_zero_of_constant_positive
    (R : Type u) [CommRing R] {U V : TopCat.{v}} (y : U) (m : ℕ) :
    HomologicalComplex.homologyMap
        (singularCochainMap R (TopCat.ofHom (ContinuousMap.const V y))) (m + 1) = 0 := by
  let pt : TopCat.{v} := TopCat.of PUnit
  let p : V ⟶ pt := TopCat.ofHom (ContinuousMap.const V PUnit.unit)
  let q : pt ⟶ U := TopCat.ofHom (ContinuousMap.const PUnit y)
  have hcomp : p ≫ q = TopCat.ofHom (ContinuousMap.const V y) := by
    ext x
    rfl
  calc
    HomologicalComplex.homologyMap
        (singularCochainMap R (TopCat.ofHom (ContinuousMap.const V y))) (m + 1)
        = HomologicalComplex.homologyMap (singularCochainMap R (p ≫ q)) (m + 1) := by
          rw [hcomp]
    _ = HomologicalComplex.homologyMap
          (singularCochainMap R q ≫ singularCochainMap R p) (m + 1) := by
          rw [singularCochainMap_comp]
    _ = HomologicalComplex.homologyMap (singularCochainMap R q) (m + 1) ≫
          HomologicalComplex.homologyMap (singularCochainMap R p) (m + 1) := by
          exact
            HomologicalComplex.homologyMap_comp
              (φ := singularCochainMap R q)
              (ψ := singularCochainMap R p) (i := m + 1)
    _ = 0 := by
          have hpoint :
              IsZero (SingularCohomology R (TopCat.of PUnit.{v+1}) (m + 1)) :=
            singularCohomology_point_positive_isZero (R := R) (m := m)
          have hq_zero :
              HomologicalComplex.homologyMap (singularCochainMap R q) (m + 1) = 0 :=
            hpoint.eq_of_tgt _ _
          rw [hq_zero, zero_comp]

/--
%%handwave
name:
  Null-homotopic maps induce zero on positive-degree singular cohomology
statement:
  If \(i:V\to U\) is null-homotopic, then the induced map
  \(i^*:H^{m+1}(U;R)\to H^{m+1}(V;R)\) is zero.
proof:
  Homotopy invariance identifies \(i^*\) with pullback along a constant map.
  The latter factors through a point, whose positive-degree singular
  cohomology vanishes.
-/
theorem singularCohomologyMap_eq_zero_of_nullhomotopic_positive
    (R : Type u) [CommRing R] {U V : TopCat.{v}} (i : V ⟶ U)
    (hi : i.hom.Nullhomotopic) (m : ℕ) :
    HomologicalComplex.homologyMap (singularCochainMap R i) (m + 1) = 0 := by
  rcases hi with ⟨y, hy⟩
  let c : V ⟶ U := TopCat.ofHom (ContinuousMap.const V y)
  rcases hy with ⟨H⟩
  have hH : TopCat.Homotopy i c := by
    simpa [c, TopCat.Homotopy] using H
  calc
    HomologicalComplex.homologyMap (singularCochainMap R i) (m + 1)
        = HomologicalComplex.homologyMap (singularCochainMap R c) (m + 1) := by
          exact singularCohomologyMap_eq_of_homotopy_on_homologyMap R hH (m + 1)
    _ = 0 := by
          simpa [c] using singularCohomologyMap_eq_zero_of_constant_positive R y m

/--
%%handwave
name:
  Null-homotopic restrictions make closed positive-degree cochains exact
statement:
  If \(i:V\to U\) is null-homotopic and \(\alpha\) is a closed real singular
  \((m+1)\)-cochain on \(U\), then \(i^*\alpha\) is a coboundary on \(V\).
proof:
  The pullback \(i^*\) on singular cohomology agrees with pullback along a
  constant map.  In positive degree a constant map factors through a point and
  induces the zero map, so the cohomology class of \(i^*\alpha\) vanishes.
  Unwinding the definition of cohomology gives a primitive cochain.
-/
theorem singularCochainMap_lift_closed_of_nullhomotopic_positive
    {U V : TopCat.{v}} (i : V ⟶ U) (hi : i.hom.Nullhomotopic)
    (m : ℕ)
    (α : (SingularCochainComplex ℝ U).X (m + 1))
    (hα : (SingularCochainComplex ℝ U).d (m + 1) (m + 2) α = 0) :
    ∃ β : (SingularCochainComplex ℝ V).X m,
      (SingularCochainComplex ℝ V).d m (m + 1) β =
        (singularCochainMap ℝ i).f (m + 1) α := by
  exact
    cochainMap_lift_closed_of_homologyMap_zero ℝ (singularCochainMap ℝ i) m
      (singularCohomologyMap_eq_zero_of_nullhomotopic_positive ℝ i hi m)
      α hα

/--
%%handwave
name:
  Locally contractible spaces have null-homotopic open restrictions
statement:
  If \(X\) is locally contractible, then every open neighborhood \(U\) of a
  point \(x\) contains an open neighborhood \(V\) of \(x\) such that the
  inclusion \(V\hookrightarrow U\) is null-homotopic.
proof:
  Apply local contractibility to \(U\), obtaining a neighborhood whose
  inclusion in \(U\) is null-homotopic.  Then choose an open neighborhood
  inside it.  Precomposing a null-homotopic map by an inclusion remains
  null-homotopic.
-/
theorem locallyContractible_exists_open_subset_nullhomotopic_inclusion
    (X : TopCat.{v}) (hloc : LocallyContractibleSpace X)
    (x : X) (U : Opens X) (hxU : x ∈ U) :
    ∃ (V : Opens X), x ∈ V ∧ ∃ (hVU : V ≤ U),
      (((Opens.toTopCat X).map (homOfLE hVU)).hom).Nullhomotopic := by
  have hUnhds : (U : Set X) ∈ 𝓝 x := U.2.mem_nhds hxU
  rcases hloc x (U : Set X) hUnhds with ⟨Vset, hVUset, hVnhds, hnull⟩
  rcases mem_nhds_iff.mp hVnhds with ⟨Wset, hWV, hWopen, hxW⟩
  let W : Opens X := ⟨Wset, hWopen⟩
  have hWU : W ≤ U := by
    intro y hy
    exact hVUset (hWV hy)
  refine ⟨W, hxW, hWU, ?_⟩
  have hWVset : (W : Set X) ⊆ Vset := hWV
  have hcomp :
      ((ContinuousMap.inclusion hVUset).comp
        (ContinuousMap.inclusion hWVset)).Nullhomotopic :=
    hnull.comp_left (ContinuousMap.inclusion hWVset)
  convert hcomp using 1

/--
%%handwave
name:
  Null-homotopic open restrictions give local primitives of cochain germs
statement:
  Suppose every open neighborhood of every point contains a smaller open
  neighborhood whose inclusion is null-homotopic.  Then every closed germ in
  a positive-degree stalk of the open singular-cochain presheaf complex has a
  primitive germ.
proof:
  Represent the closed germ by a singular cochain on an open neighborhood.
  Shrink once so that the coboundary vanishes as an actual restricted
  cochain, then shrink again so that the inclusion is null-homotopic.  The
  null-homotopic restriction calculation gives a primitive on the smaller
  open set, whose germ is the desired primitive.
-/
theorem realSingularCochainOpenPresheafComplex_stalk_lift_closed_germ_of_nullhomotopic_basis
    (X : TopCat.{v})
    (hshrink : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ (V : Opens X), x ∈ V ∧ ∃ (hVU : V ≤ U),
        (((Opens.toTopCat X).map (homOfLE hVU)).hom).Nullhomotopic)
    (m : ℕ) (x : X) :
    let S : ShortComplex AddCommGrpCat.{v} :=
      realSingularCochainOpenPresheafComplexStalkShortComplex (X := X) m x
    ∀ η : S.X₂, S.g η = 0 → ∃ θ : S.X₁, S.f θ = η := by
  intro S η hη
  let Pnp1 : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X (m + 1)
  let Pnp2 : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X (m + 2)
  let Pn : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X m
  rcases Pnp1.exists_germ_eq η with ⟨U, hxU, alpha, halpha⟩
  have hη_map :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map
        ((realSingularCochainOpenPresheafComplex X).d (m + 1) (m + 2)))
          (Pnp1.germ U x hxU alpha) = 0 := by
    rw [halpha]
    simpa [S, realSingularCochainOpenPresheafComplexStalkShortComplex, Pnp1, Pnp2]
      using hη
  have hclosed_germ :
      Pnp2.germ U x hxU
          (((realSingularCochainOpenPresheafComplex X).d (m + 1) (m + 2)).app
            (Opposite.op U) alpha) =
        Pnp2.germ U x hxU 0 := by
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hη_map
    calc
      Pnp2.germ U x hxU
          (((realSingularCochainOpenPresheafComplex X).d (m + 1) (m + 2)).app
            (Opposite.op U) alpha) = 0 := by
        simpa [Pnp2] using hη_map
      _ = Pnp2.germ U x hxU 0 := by simp
  rcases Pnp2.germ_eq x hxU hxU
      (((realSingularCochainOpenPresheafComplex X).d (m + 1) (m + 2)).app
        (Opposite.op U) alpha) 0 hclosed_germ with
    ⟨W₀, hxW₀, iW₀U, iW₀U', hclosed_restrict⟩
  have hclosed_restrict' :
      Pnp2.map iW₀U.op
          (((realSingularCochainOpenPresheafComplex X).d (m + 1) (m + 2)).app
            (Opposite.op U) alpha) = 0 := by
    simpa [Subsingleton.elim iW₀U' iW₀U] using hclosed_restrict
  let iTopW₀U : (Opens.toTopCat X).obj W₀ ⟶ (Opens.toTopCat X).obj U :=
    (Opens.toTopCat X).map iW₀U
  let alphaW₀ :
      (SingularCochainComplex ℝ ((Opens.toTopCat X).obj W₀)).X (m + 1) :=
    (singularCochainMap ℝ iTopW₀U).f (m + 1) alpha
  have hrestrict_after_d :
      (singularCochainMap ℝ iTopW₀U).f (m + 2)
        (((SingularCochainComplex ℝ ((Opens.toTopCat X).obj U)).d
          (m + 1) (m + 2)) alpha) = 0 := by
    simpa [iTopW₀U, Pnp1, Pnp2, realSingularCochainOpenPresheafComplex,
      realSingularCochainOpenComplexFunctor, realSingularCochainOpenModuleComplexFunctor,
      realSingularCochainComplexAddFunctor] using hclosed_restrict'
  have hclosedW₀ :
      (SingularCochainComplex ℝ ((Opens.toTopCat X).obj W₀)).d
          (m + 1) (m + 2) alphaW₀ = 0 := by
    have hcomm := (singularCochainMap ℝ iTopW₀U).comm (m + 1) (m + 2)
    change
      (ConcreteCategory.hom
        ((singularCochainMap ℝ iTopW₀U).f (m + 1) ≫
          (SingularCochainComplex ℝ ((Opens.toTopCat X).obj W₀)).d
            (m + 1) (m + 2))) alpha = 0
    rw [hcomm, ConcreteCategory.comp_apply]
    exact hrestrict_after_d
  rcases hshrink x W₀ hxW₀ with ⟨V, hxV, hVW₀, hnull⟩
  let iTopVW₀ : (Opens.toTopCat X).obj V ⟶ (Opens.toTopCat X).obj W₀ :=
    (Opens.toTopCat X).map (homOfLE hVW₀)
  rcases singularCochainMap_lift_closed_of_nullhomotopic_positive
      iTopVW₀ hnull m alphaW₀ hclosedW₀ with
    ⟨beta, hbeta⟩
  refine ⟨Pn.germ V x hxV beta, ?_⟩
  have hmap_theta :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map
        ((realSingularCochainOpenPresheafComplex X).d m (m + 1)))
          (Pn.germ V x hxV beta) =
        Pnp1.germ V x hxV
          (((realSingularCochainOpenPresheafComplex X).d m (m + 1)).app
            (Opposite.op V) beta) := by
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have hgerm_beta :
      Pnp1.germ V x hxV
          (((realSingularCochainOpenPresheafComplex X).d m (m + 1)).app
            (Opposite.op V) beta) =
        Pnp1.germ V x hxV
          ((singularCochainMap ℝ iTopVW₀).f (m + 1) alphaW₀) := by
    simpa [iTopVW₀, Pn, Pnp1, realSingularCochainOpenPresheafComplex,
      realSingularCochainOpenComplexFunctor, realSingularCochainOpenModuleComplexFunctor,
      realSingularCochainComplexAddFunctor] using congrArg (Pnp1.germ V x hxV) hbeta
  have hgerm_restrict_W₀ :
      Pnp1.germ V x hxV
          ((singularCochainMap ℝ iTopVW₀).f (m + 1) alphaW₀) =
        Pnp1.germ W₀ x hxW₀ alphaW₀ := by
    simpa [iTopVW₀, alphaW₀, Pnp1, realSingularCochainOpenPresheafComplex,
      realSingularCochainOpenComplexFunctor, realSingularCochainOpenModuleComplexFunctor,
      realSingularCochainComplexAddFunctor] using
      (Pnp1.germ_res_apply' (homOfLE hVW₀).op x hxV alphaW₀)
  have hgerm_restrict_U :
      Pnp1.germ W₀ x hxW₀ alphaW₀ =
        Pnp1.germ U x hxU alpha := by
    simpa [iTopW₀U, alphaW₀, Pnp1, realSingularCochainOpenPresheafComplex,
      realSingularCochainOpenComplexFunctor, realSingularCochainOpenModuleComplexFunctor,
      realSingularCochainComplexAddFunctor] using
      (Pnp1.germ_res_apply' iW₀U.op x hxW₀ alpha)
  have hf_eq :
      S.f (Pn.germ V x hxV beta) =
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map
          ((realSingularCochainOpenPresheafComplex X).d m (m + 1)))
            (Pn.germ V x hxV beta) := by
    rfl
  exact hf_eq.trans
    (hmap_theta.trans
      (hgerm_beta.trans
        (hgerm_restrict_W₀.trans
          (hgerm_restrict_U.trans halpha))))

/--
%%handwave
name:
  Open singular-cochain germs have local primitives on locally contractible spaces
statement:
  On a locally contractible space, every closed germ in a positive-degree
  stalk of the open singular-cochain presheaf complex has a primitive germ.
proof:
  Use [locally contractible spaces have null-homotopic open restrictions](lean:JJMath.Cohomology.locallyContractible_exists_open_subset_nullhomotopic_inclusion), and then apply the local primitive argument for such restrictions.
-/
theorem realSingularCochainOpenPresheafComplex_stalk_lift_closed_germ_of_locallyContractible
    (X : TopCat.{v})
    (hloc : LocallyContractibleSpace X)
    (m : ℕ) (x : X) :
    let S : ShortComplex AddCommGrpCat.{v} :=
      realSingularCochainOpenPresheafComplexStalkShortComplex (X := X) m x
    ∀ η : S.X₂, S.g η = 0 → ∃ θ : S.X₁, S.f θ = η := by
  exact
    realSingularCochainOpenPresheafComplex_stalk_lift_closed_germ_of_nullhomotopic_basis
      (X := X)
      (fun x U hxU =>
        locallyContractible_exists_open_subset_nullhomotopic_inclusion
          (X := X) hloc x U hxU)
      m x

/--
%%handwave
name:
  The sheafification unit on stalked singular-cochain complexes
statement:
  The degreewise sheafification map from open singular cochains to sheafified
  open singular cochains induces a cochain map after taking the stalk at a
  point.
proof:
  Apply the natural transformation from a presheaf to its sheafification to
  the open singular-cochain complex, then apply the stalk functor
  degreewise.
-/
def realSingularCochainSheafificationUnitStalkComplexMap
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (x : X) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (realSingularCochainOpenPresheafComplex X) ⟶
    ((TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (realSingularCochainSheafComplex X) := by
  let Kpre : CochainComplex (TopCat.Presheaf AddCommGrpCat.{v} X) ℕ :=
    realSingularCochainOpenPresheafComplex X
  let unit : Kpre ⟶
      ((CategoryTheory.sheafification (Opens.grothendieckTopology X)
        AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj Kpre :=
    (NatTrans.mapHomologicalComplex
      (CategoryTheory.toSheafification (Opens.grothendieckTopology X)
        AddCommGrpCat.{v})
      (ComplexShape.up ℕ)).app Kpre
  exact ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).mapHomologicalComplex
      (ComplexShape.up ℕ)).map unit

/--
%%handwave
name:
  Sheafification is an isomorphism on singular-cochain stalks
statement:
  In every degree, the stalk map from open singular cochains to sheafified
  open singular cochains induced by sheafification is an isomorphism.
proof:
  This is the standard fact that the map from a presheaf to its
  sheafification is an isomorphism on ordinary topological stalks.
-/
theorem realSingularCochainSheafificationUnitStalkComplexMap_f_isIso
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (x : X) (n : ℕ) :
    IsIso ((realSingularCochainSheafificationUnitStalkComplexMap X x).f n) := by
  dsimp [realSingularCochainSheafificationUnitStalkComplexMap]
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{v}
    ((realSingularCochainOpenPresheafComplex X).X n)

/--
%%handwave
name:
  Sheafification is an isomorphism on positive-degree stalk short complexes
statement:
  The sheafification map identifies the explicit stalk short complex
  \(C^m\to C^{m+1}\to C^{m+2}\) of open singular cochains with the
  corresponding stalk short complex of sheafified open singular cochains.
proof:
  The short-complex morphism induced by the stalked sheafification-unit
  cochain map is an isomorphism because each of its three component maps is
  an isomorphism on stalks.
-/
theorem realSingularCochainSheafificationUnitStalkShortComplex_isIso
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (m : ℕ) (x : X) :
    IsIso (((HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{v}
      (ComplexShape.up ℕ) m (m + 1) (m + 2)).map
        (realSingularCochainSheafificationUnitStalkComplexMap X x))) := by
  let φ := realSingularCochainSheafificationUnitStalkComplexMap X x
  let ψ := ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{v}
      (ComplexShape.up ℕ) m (m + 1) (m + 2)).map φ)
  change IsIso ψ
  haveI : IsIso ψ.τ₁ := by
    dsimp [ψ, φ, HomologicalComplex.shortComplexFunctor']
    exact realSingularCochainSheafificationUnitStalkComplexMap_f_isIso X x m
  haveI : IsIso ψ.τ₂ := by
    dsimp [ψ, φ, HomologicalComplex.shortComplexFunctor']
    exact realSingularCochainSheafificationUnitStalkComplexMap_f_isIso X x (m + 1)
  haveI : IsIso ψ.τ₃ := by
    dsimp [ψ, φ, HomologicalComplex.shortComplexFunctor']
    exact realSingularCochainSheafificationUnitStalkComplexMap_f_isIso X x (m + 2)
  exact ShortComplex.isIso_of_isIso ψ

/--
%%handwave
name:
  Local primitives pass from open cochain presheaves to sheafifications
statement:
  If every closed positive-degree germ of the open singular-cochain presheaf
  complex has a primitive, then the same is true after degreewise
  sheafification.
proof:
  Stalks of the sheafification are canonically identified with stalks of the
  original presheaf, and these identifications commute with the singular
  coboundary maps.  Transport the primitive across these stalk
  identifications.
-/
theorem realSingularCochainSheafComplex_stalk_lift_closed_germ_of_openPresheaf
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (m : ℕ) (x : X)
    (hpre :
      let S : ShortComplex AddCommGrpCat.{v} :=
        realSingularCochainOpenPresheafComplexStalkShortComplex (X := X) m x
      ∀ η : S.X₂, S.g η = 0 → ∃ θ : S.X₁, S.f θ = η) :
    let S : ShortComplex AddCommGrpCat.{v} :=
      realSingularCochainSheafComplexStalkShortComplex
        (X := X) m x
    ∀ η : S.X₂, S.g η = 0 → ∃ θ : S.X₁, S.f θ = η := by
  intro S η hη
  let Spre : ShortComplex AddCommGrpCat.{v} :=
    realSingularCochainOpenPresheafComplexStalkShortComplex (X := X) m x
  have hpreExact : Spre.Exact := by
    change Spre.Exact
    rw [ShortComplex.ab_exact_iff]
    exact hpre
  let Ksh : CochainComplex AddCommGrpCat.{v} ℕ :=
    ((TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (realSingularCochainSheafComplex X)
  have hExpSheaf : (Ksh.sc' m (m + 1) (m + 2)).Exact := by
    let φ := realSingularCochainSheafificationUnitStalkComplexMap X x
    let ψ := ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{v}
      (ComplexShape.up ℕ) m (m + 1) (m + 2)).map φ)
    haveI : IsIso ψ := by
      dsimp [ψ]
      exact realSingularCochainSheafificationUnitStalkShortComplex_isIso X m x
    exact ShortComplex.exact_of_iso (asIso ψ) hpreExact
  have hExact : S.Exact := by
    change (Ksh.sc (m + 1)).Exact
    change Ksh.ExactAt (m + 1)
    exact
      (HomologicalComplex.exactAt_iff' (K := Ksh) (i := m) (j := m + 1) (k := m + 2)
        (CochainComplex.prev_nat_succ m) (CochainComplex.next ℕ (m + 1))).2 hExpSheaf
  rw [ShortComplex.ab_exact_iff] at hExact
  exact hExact η hη

/--
%%handwave
name:
  Closed positive-degree singular-cochain germs have local primitives
statement:
  On a locally contractible space, every closed germ in a positive-degree
  stalk of the sheafified open singular-cochain complex has a primitive germ.
proof:
  Represent the closed germ by a singular cochain on an open neighborhood.
  Local contractibility permits restriction to a smaller neighborhood whose
  inclusion into the original one is null-homotopic.  Homotopy invariance of
  singular cohomology makes the restricted cohomology class vanish by
  [the null-homotopic restriction calculation](lean:JJMath.Cohomology.singularCochainMap_lift_closed_of_nullhomotopic_positive).  The sheafification and stalk maps identify this restricted primitive with a primitive germ.
-/
theorem realSingularCochainSheafComplex_stalk_lift_closed_germ_of_locallyContractible
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (hloc : LocallyContractibleSpace X)
    (m : ℕ) (x : X) :
    let S : ShortComplex AddCommGrpCat.{v} :=
      realSingularCochainSheafComplexStalkShortComplex
        (X := X) m x
    ∀ η : S.X₂, S.g η = 0 → ∃ θ : S.X₁, S.f θ = η := by
  exact
    realSingularCochainSheafComplex_stalk_lift_closed_germ_of_openPresheaf
      (X := X) m x
      (realSingularCochainOpenPresheafComplex_stalk_lift_closed_germ_of_locallyContractible
        (X := X) hloc m x)

/--
%%handwave
name:
  Positive-degree singular-cochain stalks are exact on locally contractible spaces
statement:
  On a locally contractible space, every positive-degree short complex in the
  stalk of the sheafified open singular-cochain complex is exact.
proof:
  Represent a closed germ by a singular cochain on an open neighborhood.
  Local contractibility permits restriction to a smaller neighborhood whose
  inclusion into the original one is null-homotopic.  The induced pullback on
  positive-degree singular cohomology is therefore zero, so after restriction
  the closed cochain is a coboundary.
-/
theorem realSingularCochainSheafComplex_stalk_exactAt_succ_of_locallyContractible
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (hloc : LocallyContractibleSpace X)
    (m : ℕ) (x : X) :
    (realSingularCochainSheafComplexStalkShortComplex
      (X := X) m x).Exact := by
  let S : ShortComplex AddCommGrpCat.{v} :=
    realSingularCochainSheafComplexStalkShortComplex
      (X := X) m x
  change S.Exact
  rw [ShortComplex.ab_exact_iff]
  exact
    realSingularCochainSheafComplex_stalk_lift_closed_germ_of_locallyContractible
      (X := X) hloc m x

/--
%%handwave
name:
  Null-homotopic restrictions make closed zero-cochains locally constant
statement:
  If \(V\subset U\) is an open inclusion whose associated map is
  null-homotopic, then the restriction to \(V\) of a closed singular
  zero-cochain on \(U\) is a constant zero-cochain.
proof:
  A closed singular zero-cochain is constant on singular one-simplices.  Along
  a null-homotopy of the inclusion, every point of \(V\) is joined in \(U\) to
  the chosen contraction point, so the restricted zero-cochain has the same
  value on every singular zero-simplex in \(V\).  This identifies it with the
  constant zero-cochain of that value.
-/
theorem singularCochainMap_closed_zero_eq_constant_of_nullhomotopic_openRestriction
    (X : TopCat.{v}) {U V : Opens X} (hVU : V ≤ U)
    (hnull : (((Opens.toTopCat X).map (homOfLE hVU)).hom).Nullhomotopic)
    (α : (SingularCochainComplex ℝ ((Opens.toTopCat X).obj U)).X 0)
    (hα :
      (SingularCochainComplex ℝ ((Opens.toTopCat X).obj U)).d 0 1 α = 0) :
    ∃ c : (realConstantOpenPresheaf X).obj (Opposite.op V),
      (singularCochainMap ℝ ((Opens.toTopCat X).map (homOfLE hVU))).f 0 α =
        (realConstantOpenPresheafToSingularCochainZeroPresheaf X).app
          (Opposite.op V) c := by
  exact
    (Classical.choose_spec
      (realConstantOpenPresheafToSingularCochainZeroPresheaf_full_spec X)).2.1
        hVU hnull α hα

/--
%%handwave
name:
  The presheaf augmentation is exact on degree-zero stalks from null-homotopic restrictions
statement:
  Suppose every open neighborhood of every point contains a smaller open
  neighborhood whose inclusion is null-homotopic.  Then the stalk sequence
  of constant real functions, singular zero-cochains, and singular
  one-cochains is exact.
proof:
  Represent a closed zero-cochain germ by a zero-cochain on an open
  neighborhood.  Shrink once so that the coboundary vanishes as an actual
  restricted one-cochain, then shrink again to a null-homotopic inclusion.
  The degree-zero null-homotopic restriction result says the restricted
  zero-cochain is a constant zero-cochain, and the equality of restricted
  germs gives the required preimage in the constant stalk.
-/
theorem realSingularCochainOpenPresheafAugmentationStalkShortComplex_exact_of_nullhomotopic_basis
    (X : TopCat.{v})
    (hshrink : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ (V : Opens X), x ∈ V ∧ ∃ (hVU : V ≤ U),
        (((Opens.toTopCat X).map (homOfLE hVU)).hom).Nullhomotopic) :
    ∀ x : X,
      (realSingularCochainOpenPresheafAugmentationStalkShortComplex
        (X := X) x).Exact := by
  intro x
  let S : ShortComplex AddCommGrpCat.{v} :=
    realSingularCochainOpenPresheafAugmentationStalkShortComplex
      (X := X) x
  change S.Exact
  rw [ShortComplex.ab_exact_iff]
  intro η hη
  let Pconst : TopCat.Presheaf AddCommGrpCat.{v} X :=
    realConstantOpenPresheaf X
  let P₀ : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X 0
  let P₁ : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X 1
  let aug : Pconst ⟶ P₀ :=
    realConstantOpenPresheafToSingularCochainZeroPresheaf X
  let d₀₁ : P₀ ⟶ P₁ :=
    (realSingularCochainOpenPresheafComplex X).d 0 1
  rcases P₀.exists_germ_eq η with ⟨U, hxU, alpha, halpha⟩
  have hη_map :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map d₀₁)
          (P₀.germ U x hxU alpha) = 0 := by
    rw [halpha]
    simpa [S, realSingularCochainOpenPresheafAugmentationStalkShortComplex,
      realSingularCochainOpenPresheafAugmentationShortComplex, P₀, P₁, d₀₁]
      using hη
  have hclosed_germ :
      P₁.germ U x hxU (d₀₁.app (Opposite.op U) alpha) =
        P₁.germ U x hxU 0 := by
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hη_map
    calc
      P₁.germ U x hxU (d₀₁.app (Opposite.op U) alpha) = 0 := by
        simpa [P₁, d₀₁] using hη_map
      _ = P₁.germ U x hxU 0 := by simp
  rcases P₁.germ_eq x hxU hxU
      (d₀₁.app (Opposite.op U) alpha) 0 hclosed_germ with
    ⟨W₀, hxW₀, iW₀U, iW₀U', hclosed_restrict⟩
  have hclosed_restrict' :
      P₁.map iW₀U.op (d₀₁.app (Opposite.op U) alpha) = 0 := by
    simpa [Subsingleton.elim iW₀U' iW₀U] using hclosed_restrict
  let iTopW₀U : (Opens.toTopCat X).obj W₀ ⟶ (Opens.toTopCat X).obj U :=
    (Opens.toTopCat X).map iW₀U
  let alphaW₀ :
      (SingularCochainComplex ℝ ((Opens.toTopCat X).obj W₀)).X 0 :=
    (singularCochainMap ℝ iTopW₀U).f 0 alpha
  have hrestrict_after_d :
      (singularCochainMap ℝ iTopW₀U).f 1
        (((SingularCochainComplex ℝ ((Opens.toTopCat X).obj U)).d
          0 1) alpha) = 0 := by
    simpa [iTopW₀U, P₀, P₁, d₀₁, realSingularCochainOpenPresheafComplex,
      realSingularCochainOpenComplexFunctor, realSingularCochainOpenModuleComplexFunctor,
      realSingularCochainComplexAddFunctor] using hclosed_restrict'
  have hclosedW₀ :
      (SingularCochainComplex ℝ ((Opens.toTopCat X).obj W₀)).d
          0 1 alphaW₀ = 0 := by
    have hcomm := (singularCochainMap ℝ iTopW₀U).comm 0 1
    change
      (ConcreteCategory.hom
        ((singularCochainMap ℝ iTopW₀U).f 0 ≫
          (SingularCochainComplex ℝ ((Opens.toTopCat X).obj W₀)).d
            0 1)) alpha = 0
    rw [hcomm, ConcreteCategory.comp_apply]
    exact hrestrict_after_d
  rcases hshrink x W₀ hxW₀ with ⟨V, hxV, hVW₀, hnull⟩
  let iTopVW₀ : (Opens.toTopCat X).obj V ⟶ (Opens.toTopCat X).obj W₀ :=
    (Opens.toTopCat X).map (homOfLE hVW₀)
  rcases
      singularCochainMap_closed_zero_eq_constant_of_nullhomotopic_openRestriction
        (X := X) hVW₀ hnull alphaW₀ hclosedW₀ with
    ⟨c, hc⟩
  refine ⟨Pconst.germ V x hxV c, ?_⟩
  have hmap_theta :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map aug)
          (Pconst.germ V x hxV c) =
        P₀.germ V x hxV (aug.app (Opposite.op V) c) := by
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have hgerm_const :
      P₀.germ V x hxV (aug.app (Opposite.op V) c) =
        P₀.germ V x hxV
          ((singularCochainMap ℝ iTopVW₀).f 0 alphaW₀) := by
    simpa [iTopVW₀, aug, P₀] using congrArg (P₀.germ V x hxV) hc.symm
  have hgerm_restrict_W₀ :
      P₀.germ V x hxV
          ((singularCochainMap ℝ iTopVW₀).f 0 alphaW₀) =
        P₀.germ W₀ x hxW₀ alphaW₀ := by
    simpa [iTopVW₀, alphaW₀, P₀, realSingularCochainOpenPresheafComplex,
      realSingularCochainOpenComplexFunctor, realSingularCochainOpenModuleComplexFunctor,
      realSingularCochainComplexAddFunctor] using
      (P₀.germ_res_apply' (homOfLE hVW₀).op x hxV alphaW₀)
  have hgerm_restrict_U :
      P₀.germ W₀ x hxW₀ alphaW₀ =
        P₀.germ U x hxU alpha := by
    simpa [iTopW₀U, alphaW₀, P₀, realSingularCochainOpenPresheafComplex,
      realSingularCochainOpenComplexFunctor, realSingularCochainOpenModuleComplexFunctor,
      realSingularCochainComplexAddFunctor] using
      (P₀.germ_res_apply' iW₀U.op x hxW₀ alpha)
  have hf_eq :
      S.f (Pconst.germ V x hxV c) =
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map aug)
          (Pconst.germ V x hxV c) := by
    rfl
  exact hf_eq.trans
    (hmap_theta.trans
      (hgerm_const.trans
        (hgerm_restrict_W₀.trans
          (hgerm_restrict_U.trans halpha))))

/--
%%handwave
name:
  The presheaf augmentation is exact on degree-zero stalks
statement:
  On a locally contractible space, the stalk at any point of the presheaf
  complex consisting of constant real functions, singular zero-cochains, and
  singular one-cochains is exact.
proof:
  Represent a closed zero-cochain germ on an open neighborhood.  Shrink first
  so its coboundary vanishes as an actual restricted cochain, then shrink to
  a smaller neighborhood whose inclusion is null-homotopic.  On that smaller
  neighborhood, homotopy invariance in degree zero identifies the restricted
  zero-cocycle with a constant zero-cochain.
-/
theorem realSingularCochainOpenPresheafAugmentationStalkShortComplex_exact_of_locallyContractible
    (X : TopCat.{v}) (hloc : LocallyContractibleSpace X) :
    ∀ x : X,
      (realSingularCochainOpenPresheafAugmentationStalkShortComplex
        (X := X) x).Exact := by
  exact
    realSingularCochainOpenPresheafAugmentationStalkShortComplex_exact_of_nullhomotopic_basis
      (X := X)
      (fun x U hxU =>
        locallyContractible_exists_open_subset_nullhomotopic_inclusion
          (X := X) hloc x U hxU)

/--
%%handwave
name:
  Degree-zero presheaf exactness passes through sheafification
statement:
  If the presheaf degree-zero augmented singular-cochain stalk complex is
  exact at a point, then the corresponding stalk complex after sheafification
  is exact at that point.
proof:
  The sheafification map induces isomorphisms on the stalks of the constant
  presheaf and of the singular cochain presheaves in degrees zero and one.
  These three isomorphisms identify the presheaf and sheafified augmented
  short complexes, and exactness is invariant under isomorphism of short
  complexes.
-/
theorem sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains_stalkwise_zero_exact_of_openPresheaf_exact
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (x : X)
    (hpre :
      (realSingularCochainOpenPresheafAugmentationStalkShortComplex
        (X := X) x).Exact) :
    (sheafifiedOpenRealSingularCochainSheafAugmentationStalkShortComplex
      (X := X) hloc
      (sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains
        (X := X) hloc) x).Exact := by
  let J := Opens.grothendieckTopology X
  let η : realConstantOpenPresheaf X ⟶
      (realSingularCochainOpenPresheafComplex X).X 0 :=
    realConstantOpenPresheafToSingularCochainZeroPresheaf X
  let P : TopCat.Presheaf AddCommGrpCat.{v} X := realConstantOpenPresheaf X
  let Q₀ : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X 0
  let Q₁ : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X 1
  let d₀₁ : Q₀ ⟶ Q₁ := (realSingularCochainOpenPresheafComplex X).d 0 1
  let st := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x
  let uP : st.obj P ⟶ st.obj (CategoryTheory.sheafify J P) :=
    st.map (CategoryTheory.toSheafify J P)
  let uQ₀ : st.obj Q₀ ⟶ st.obj (CategoryTheory.sheafify J Q₀) :=
    st.map (CategoryTheory.toSheafify J Q₀)
  let uQ₁ : st.obj Q₁ ⟶ st.obj (CategoryTheory.sheafify J Q₁) :=
    st.map (CategoryTheory.toSheafify J Q₁)
  let Spre : ShortComplex AddCommGrpCat.{v} :=
    realSingularCochainOpenPresheafAugmentationStalkShortComplex (X := X) x
  let Ssh : ShortComplex AddCommGrpCat.{v} :=
    sheafifiedOpenRealSingularCochainSheafAugmentationStalkShortComplex
      (X := X) hloc
      (sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains
        (X := X) hloc) x
  change Ssh.Exact
  have instUP : IsIso uP := by
    dsimp [uP, P, J]
    exact
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        x AddCommGrpCat.{v} (realConstantOpenPresheaf X)
  have instUQ₀ : IsIso uQ₀ := by
    dsimp [uQ₀, Q₀, J]
    exact
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        x AddCommGrpCat.{v}
        ((realSingularCochainOpenPresheafComplex X).X 0)
  have instUQ₁ : IsIso uQ₁ := by
    dsimp [uQ₁, Q₁, J]
    exact
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        x AddCommGrpCat.{v}
        ((realSingularCochainOpenPresheafComplex X).X 1)
  let eP : st.obj P ≅ st.obj (CategoryTheory.sheafify J P) := by
    letI : IsIso uP := instUP
    exact asIso uP
  let eQ₀ : st.obj Q₀ ≅ st.obj (CategoryTheory.sheafify J Q₀) := by
    letI : IsIso uQ₀ := instUQ₀
    exact asIso uQ₀
  let eQ₁ : st.obj Q₁ ≅ st.obj (CategoryTheory.sheafify J Q₁) := by
    letI : IsIso uQ₁ := instUQ₁
    exact asIso uQ₁
  have hnatη :
      st.map η ≫ uQ₀ =
        uP ≫ st.map (CategoryTheory.sheafifyMap J η) := by
    calc
      st.map η ≫ uQ₀
          = st.map (η ≫ CategoryTheory.toSheafify J Q₀) := by
              dsimp [uQ₀]
              exact (st.map_comp _ _).symm
      _ = st.map (CategoryTheory.toSheafify J P ≫
            CategoryTheory.sheafifyMap J η) := by
              exact congrArg st.map
                (CategoryTheory.toSheafify_naturality (J := J) (η := η))
      _ = uP ≫ st.map (CategoryTheory.sheafifyMap J η) := by
              dsimp [uP]
              exact st.map_comp _ _
  have hnatd :
      st.map d₀₁ ≫ uQ₁ =
        uQ₀ ≫ st.map (CategoryTheory.sheafifyMap J d₀₁) := by
    calc
      st.map d₀₁ ≫ uQ₁
          = st.map (d₀₁ ≫ CategoryTheory.toSheafify J Q₁) := by
              dsimp [uQ₁]
              exact (st.map_comp _ _).symm
      _ = st.map (CategoryTheory.toSheafify J Q₀ ≫
            CategoryTheory.sheafifyMap J d₀₁) := by
              exact congrArg st.map
                (CategoryTheory.toSheafify_naturality (J := J) (η := d₀₁))
      _ = uQ₀ ≫ st.map (CategoryTheory.sheafifyMap J d₀₁) := by
              dsimp [uQ₀]
              exact st.map_comp _ _
  let e : Spre ≅ Ssh :=
    ShortComplex.isoMk eP eQ₀ eQ₁
      (by
        simpa [eP, eQ₀] using hnatη.symm)
      (by
        simpa [eQ₀, eQ₁] using hnatd.symm)
  exact ShortComplex.exact_of_iso e hpre

/--
%%handwave
name:
  The standard augmentation is exact on degree-zero stalks
statement:
  For a locally contractible paracompact space, the stalk at any point of
  the standard augmented singular-cochain sheaf complex is exact in degree
  zero.
proof:
  A closed singular zero-cochain germ is locally constant.  Represent the
  germ on an open neighborhood and shrink to a smaller neighborhood whose
  inclusion is null-homotopic.  On this smaller neighborhood, homotopy
  invariance identifies the closed zero-cochain with a constant zero-cochain,
  so the original germ lies in the image of the constant-sheaf germ.
-/
theorem sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains_stalkwise_zero_exact
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] :
    ∀ x : X,
      (sheafifiedOpenRealSingularCochainSheafAugmentationStalkShortComplex
        (X := X) hloc
        (sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains
          (X := X) hloc) x).Exact := by
  intro x
  exact
    sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains_stalkwise_zero_exact_of_openPresheaf_exact
      (X := X) hloc x
      (realSingularCochainOpenPresheafAugmentationStalkShortComplex_exact_of_locallyContractible
        (X := X) hloc x)

/--
%%handwave
name:
  A vanishing constant zero-cochain germ has zero constant germ
statement:
  If the singular zero-cochain germ associated to a constant real germ is
  zero, then the original constant real germ is zero.
proof:
  Evaluate the zero singular zero-cochain germ on the constant singular
  zero-simplex at the chosen point.  The value is exactly the representing
  real constant, so the representing constant germ is zero.
-/
theorem realConstantOpenPresheafToSingularCochainZeroPresheaf_germ_eq_zero_of_image_germ_eq_zero
    (X : TopCat.{v}) (x : X) (U : Opens X) (hxU : x ∈ U)
    (c : (realConstantOpenPresheaf X).obj (Opposite.op U))
    (himage :
      ((realSingularCochainOpenPresheafComplex X).X 0).germ U x hxU
        ((realConstantOpenPresheafToSingularCochainZeroPresheaf X).app
          (Opposite.op U) c) = 0) :
    (realConstantOpenPresheaf X).germ U x hxU c = 0 := by
  exact
    (Classical.choose_spec
      (realConstantOpenPresheafToSingularCochainZeroPresheaf_full_spec X)).2.2
        x U hxU c himage

/--
%%handwave
name:
  The presheaf augmentation is monic on stalks
statement:
  At every point, the stalk map from constant real germs to singular
  zero-cochain germs induced by the presheaf augmentation is injective.
proof:
  If a constant germ maps to zero, restrict to a representative open
  neighborhood where the associated constant singular zero-cochain vanishes.
  Evaluating on the constant singular zero-simplex at the point shows that
  the real constant is zero as a germ.
-/
theorem realConstantOpenPresheafToSingularCochainZeroPresheaf_stalk_mono
    (X : TopCat.{v}) :
    ∀ x : X,
      Mono
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map
          (realConstantOpenPresheafToSingularCochainZeroPresheaf X)) := by
  intro x
  rw [AddCommGrpCat.mono_iff_injective]
  intro a b hab
  let Pconst : TopCat.Presheaf AddCommGrpCat.{v} X :=
    realConstantOpenPresheaf X
  let P₀ : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X 0
  let aug : Pconst ⟶ P₀ :=
    realConstantOpenPresheafToSingularCochainZeroPresheaf X
  have hdiff_map :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map aug) (a - b) = 0 := by
    change
      (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map aug)) (a - b) = 0
    rw [map_sub, hab, sub_self]
  rcases Pconst.exists_germ_eq (a - b) with ⟨U, hxU, c, hc⟩
  have himage_germ :
      P₀.germ U x hxU (aug.app (Opposite.op U) c) = 0 := by
    have hmap_germ :
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map aug)
            (Pconst.germ U x hxU c) = 0 := by
      simpa [hc, aug] using hdiff_map
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hmap_germ
    simpa [P₀, aug] using hmap_germ
  have hconst_germ :
      Pconst.germ U x hxU c = 0 :=
    realConstantOpenPresheafToSingularCochainZeroPresheaf_germ_eq_zero_of_image_germ_eq_zero
      (X := X) x U hxU c (by simpa [P₀, aug] using himage_germ)
  have hsub : a - b = 0 := by
    simpa [hc] using hconst_germ
  exact sub_eq_zero.mp hsub

/--
%%handwave
name:
  Degree-zero presheaf monicity passes through sheafification
statement:
  If the presheaf augmentation is monic on a stalk, then the corresponding
  sheafified augmentation is monic on that stalk.
proof:
  The stalk maps from the constant presheaf and singular zero-cochain
  presheaf to their sheafifications are isomorphisms.  The sheafified
  augmentation is conjugate to the presheaf augmentation under these
  isomorphisms, so monicity transfers across the isomorphism.
-/
theorem sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains_stalkwise_mono_of_openPresheaf_mono
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (x : X)
    (hpre :
      Mono
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map
          (realConstantOpenPresheafToSingularCochainZeroPresheaf X))) :
    Mono
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map
        (sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains
          (X := X) hloc).ε.1) := by
  let J := Opens.grothendieckTopology X
  let η : realConstantOpenPresheaf X ⟶
      (realSingularCochainOpenPresheafComplex X).X 0 :=
    realConstantOpenPresheafToSingularCochainZeroPresheaf X
  let P : TopCat.Presheaf AddCommGrpCat.{v} X := realConstantOpenPresheaf X
  let Q : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X 0
  let st := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x
  let uP : st.obj P ⟶ st.obj (CategoryTheory.sheafify J P) :=
    st.map (CategoryTheory.toSheafify J P)
  let uQ : st.obj Q ⟶ st.obj (CategoryTheory.sheafify J Q) :=
    st.map (CategoryTheory.toSheafify J Q)
  let sη : st.obj (CategoryTheory.sheafify J P) ⟶
      st.obj (CategoryTheory.sheafify J Q) :=
    st.map (CategoryTheory.sheafifyMap J η)
  change Mono sη
  haveI : IsIso uP := by
    dsimp [uP, P, J]
    exact
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        x AddCommGrpCat.{v} (realConstantOpenPresheaf X)
  haveI : IsIso uQ := by
    dsimp [uQ, Q, J]
    exact
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        x AddCommGrpCat.{v}
        ((realSingularCochainOpenPresheafComplex X).X 0)
  have hnat : st.map η ≫ uQ = uP ≫ sη := by
    calc
      st.map η ≫ uQ
          = st.map (η ≫ CategoryTheory.toSheafify J Q) := by
              dsimp [uQ]
              exact (st.map_comp _ _).symm
      _ = st.map (CategoryTheory.toSheafify J P ≫
            CategoryTheory.sheafifyMap J η) := by
              exact congrArg st.map
                (CategoryTheory.toSheafify_naturality (J := J) (η := η))
      _ = uP ≫ sη := by
              dsimp [uP, sη]
              exact st.map_comp _ _
  haveI : Mono (st.map η ≫ uQ) := mono_comp _ _
  haveI : Mono (uP ≫ sη) := by
    simpa [hnat] using (inferInstance : Mono (st.map η ≫ uQ))
  exact (mono_comp_iff_of_isIso uP sη).1 inferInstance

/--
%%handwave
name:
  The standard augmentation is monic on stalks
statement:
  For a locally contractible paracompact space, the map on stalks induced by
  the standard augmentation from locally constant real germs to singular
  zero-cochain germs is injective.
proof:
  If a constant germ maps to the zero singular zero-cochain germ, then after
  restricting to a sufficiently small neighborhood the corresponding
  constant zero-cochain vanishes.  Evaluating it on any singular zero-simplex
  supported in that neighborhood shows that the constant is zero.
-/
theorem sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains_stalkwise_mono
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] :
    ∀ x : X,
      Mono
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map
          (sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains
            (X := X) hloc).ε.1) := by
  intro x
  exact
    sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains_stalkwise_mono_of_openPresheaf_mono
      (X := X) hloc x
      (realConstantOpenPresheafToSingularCochainZeroPresheaf_stalk_mono
        (X := X) x)

/--
%%handwave
name:
  The standard singular-cochain augmentation is exact on degree-zero stalks
statement:
  On a locally contractible paracompact space there is a standard
  augmentation from the real constant sheaf to sheafified singular
  zero-cochains such that, on every stalk, the sequence of constant germs,
  zero-cochain germs, and one-cochain germs is exact, and the augmentation is
  monic on every stalk.
proof:
  Construct the augmentation by sending a locally constant real section to the
  corresponding singular zero-cochain.  A closed zero-cochain germ is locally
  constant: shrink to a neighborhood whose inclusion into the original one is
  null-homotopic, then use homotopy invariance in degree zero to identify the
  restricted zero-cocycle with a constant zero-cochain.  Injectivity follows
  by evaluating the associated constant zero-cochain on a sufficiently small
  representative neighborhood.
-/
theorem exists_sheafifiedOpenRealSingularCochainSheafAugmentationData_with_stalkwise_zero_exactness_from_local_zero_cocycles
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] :
    ∃ A : SheafifiedOpenRealSingularCochainSheafAugmentationData X hloc,
      (∀ x : X,
        (sheafifiedOpenRealSingularCochainSheafAugmentationStalkShortComplex
          (X := X) hloc A x).Exact) ∧
      (∀ x : X,
        Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map A.ε.1)) := by
  refine
    ⟨sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains
        (X := X) hloc,
      ?_, ?_⟩
  · exact
      sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains_stalkwise_zero_exact
        (X := X) hloc
  · exact
      sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains_stalkwise_mono
        (X := X) hloc

/--
%%handwave
name:
  Closed singular zero-cochain germs are locally constant
statement:
  On a locally contractible paracompact space there is a standard
  augmentation of the sheafified open singular-cochain complex such that
  every closed singular zero-cochain germ comes from a constant-sheaf germ,
  and the augmentation is monic on every stalk.
proof:
  The augmentation sends a locally constant real function to the corresponding
  locally constant singular zero-cochain.  If a singular zero-cochain germ is
  closed, then after restriction along a null-homotopic neighborhood inclusion
  it is cohomologous, in degree zero, to a constant zero-cochain; since the
  cochain itself is closed, this gives equality as a germ.  The same germ
  description shows that the augmentation is injective on stalks.
-/
theorem exists_sheafifiedOpenRealSingularCochainSheafAugmentationData_with_stalkwise_zero_lifting
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] :
    ∃ A : SheafifiedOpenRealSingularCochainSheafAugmentationData X hloc,
      (∀ x : X,
        let S : ShortComplex AddCommGrpCat.{v} :=
          sheafifiedOpenRealSingularCochainSheafAugmentationStalkShortComplex
            (X := X) hloc A x
        ∀ η : S.X₂, S.g η = 0 → ∃ θ : S.X₁, S.f θ = η) ∧
      (∀ x : X,
        Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map A.ε.1)) := by
  let A : SheafifiedOpenRealSingularCochainSheafAugmentationData X hloc :=
    sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains
      (X := X) hloc
  refine ⟨A, ?_, ?_⟩
  intro x
  let S : ShortComplex AddCommGrpCat.{v} :=
    sheafifiedOpenRealSingularCochainSheafAugmentationStalkShortComplex
      (X := X) hloc A x
  have hS : S.Exact :=
    sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains_stalkwise_zero_exact
      (X := X) hloc x
  rw [ShortComplex.ab_exact_iff] at hS
  exact hS
  exact
    sheafifiedOpenRealSingularCochainSheafAugmentationDataOfConstantZeroCochains_stalkwise_mono
      (X := X) hloc

/--
%%handwave
name:
  The standard augmentation is exact and monic on stalks in degree zero
statement:
  On a locally contractible paracompact space there is a standard
  augmentation of the sheafified open singular-cochain complex such that the
  augmented degree-zero short complex is exact on every stalk and the
  augmentation is monic on every stalk.
proof:
  The augmentation sends a locally constant real function to the corresponding
  locally constant singular zero-cochain.  After passing to a stalk, local
  contractibility lets a zero-cocycle be restricted along a null-homotopic
  neighborhood inclusion, where homotopy invariance makes it equal to a
  constant zero-cochain.  Monicity is checked on the same germs.
-/
theorem exists_sheafifiedOpenRealSingularCochainSheafAugmentationData_with_stalkwise_zero_exactness
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] :
    ∃ A : SheafifiedOpenRealSingularCochainSheafAugmentationData X hloc,
      (∀ x : X,
        (sheafifiedOpenRealSingularCochainSheafAugmentationStalkShortComplex
          (X := X) hloc A x).Exact) ∧
      (∀ x : X,
        Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map A.ε.1)) := by
  rcases
      exists_sheafifiedOpenRealSingularCochainSheafAugmentationData_with_stalkwise_zero_lifting
        (X := X) hloc with
    ⟨A, hstalk_lift, hstalk_mono⟩
  refine ⟨A, ?_, hstalk_mono⟩
  intro x
  let S : ShortComplex AddCommGrpCat.{v} :=
    sheafifiedOpenRealSingularCochainSheafAugmentationStalkShortComplex
      (X := X) hloc A x
  change S.Exact
  rw [ShortComplex.ab_exact_iff]
  exact hstalk_lift x

/--
%%handwave
name:
  The standard sheafified singular-cochain augmentation is stalkwise exact
statement:
  On a locally contractible paracompact space there is a standard
  augmentation of the sheafified open singular-cochain complex such that the
  augmented degree-zero short complex is exact on every stalk, the
  augmentation is monic on every stalk, and every positive-degree short
  complex is exact on every stalk.
proof:
  The augmentation sends a locally constant real function to the corresponding
  locally constant singular zero-cochain.  At a point, every germ may be
  shrunk to a neighborhood whose inclusion in the original representative is
  null-homotopic.  Homotopy invariance makes positive-degree cocycles locally
  coboundaries, and makes degree-zero cocycles locally equal to constants.
-/
theorem exists_sheafifiedOpenRealSingularCochainSheafAugmentationData_with_stalkwise_exactness
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] :
    ∃ A : SheafifiedOpenRealSingularCochainSheafAugmentationData X hloc,
      (∀ x : X,
        (sheafifiedOpenRealSingularCochainSheafAugmentationStalkShortComplex
          (X := X) hloc A x).Exact) ∧
      (∀ x : X,
        Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map A.ε.1)) ∧
      (∀ m : ℕ, ∀ x : X,
        (realSingularCochainSheafComplexStalkShortComplex
          (X := X) m x).Exact) := by
  rcases
      exists_sheafifiedOpenRealSingularCochainSheafAugmentationData_with_stalkwise_zero_exactness
        (X := X) hloc with
    ⟨A, hstalk_zero, hstalk_mono⟩
  exact
    ⟨A, hstalk_zero, hstalk_mono,
      fun m x =>
        realSingularCochainSheafComplex_stalk_exactAt_succ_of_locallyContractible
          (X := X) hloc m x⟩

/--
%%handwave
name:
  The standard sheafified singular-cochain augmentation exists and is exact
statement:
  There is standard augmentation data for the sheafified open singular-cochain
  complex on a locally contractible space such that the degree-zero short
  complex is exact, the augmentation is monic, and the positive cochain
  complex is exact.
proof:
  Apply [there is a standard augmentation whose stalk complexes are exact](lean:JJMath.Cohomology.exists_sheafifiedOpenRealSingularCochainSheafAugmentationData_with_stalkwise_exactness).  Exactness of short complexes of sheaves and monicity of a sheaf morphism are checked on stalks.
-/
theorem exists_sheafifiedOpenRealSingularCochainSheafAugmentationData_with_exactness
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] :
    ∃ A : SheafifiedOpenRealSingularCochainSheafAugmentationData X hloc,
      ({ f := A.ε, g := (realSingularCochainSheafComplex X).d 0 1, zero := A.hε } :
          ShortComplex
            (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})).Exact ∧
        Mono A.ε ∧
        (∀ m : ℕ, (realSingularCochainSheafComplex X).ExactAt (m + 1)) := by
  rcases
      exists_sheafifiedOpenRealSingularCochainSheafAugmentationData_with_stalkwise_exactness
        (X := X) hloc with
    ⟨A, hstalk_zero, hstalk_mono, hstalk_pos⟩
  refine ⟨A, ?_, ?_, ?_⟩
  · exact
      (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
        (sheafifiedOpenRealSingularCochainSheafAugmentationShortComplex
          (X := X) hloc A)).2
        (fun x => by
          simpa [sheafifiedOpenRealSingularCochainSheafAugmentationStalkShortComplex]
            using hstalk_zero x)
  · exact (TopCat.Presheaf.mono_iff_stalk_mono A.ε).2 hstalk_mono
  · intro m
    rw [HomologicalComplex.exactAt_iff]
    exact
      (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
        ((realSingularCochainSheafComplex X).sc (m + 1))).2
        (fun x => by
          simpa [realSingularCochainSheafComplexStalkShortComplex]
            using hstalk_pos m x)

/--
%%handwave
name:
  The standard augmentation of sheafified open singular cochains exists
statement:
  The constant real sheaf maps to degree-zero sheafified open singular
  cochains by locally constant zero-cochains, this map is killed by the first
  coboundary, and it commutes with scalar multiplication.
proof:
  Forget the exactness properties in [the standard sheafified singular-cochain augmentation exists and is exact](lean:JJMath.Cohomology.exists_sheafifiedOpenRealSingularCochainSheafAugmentationData_with_exactness).
-/
theorem exists_sheafifiedOpenRealSingularCochainSheafAugmentationData
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] :
    Nonempty (SheafifiedOpenRealSingularCochainSheafAugmentationData X hloc) := by
  rcases exists_sheafifiedOpenRealSingularCochainSheafAugmentationData_with_exactness
      (X := X) hloc with
    ⟨A, _hexact_zero, _hmono_ε, _hexact_pos⟩
  exact ⟨A⟩

/--
%%handwave
name:
  The cohomology of the top open is the cohomology of the space
statement:
  The top open subset of a topological space has real singular cohomology
  linearly equivalent to the real singular cohomology of the original space.
proof:
  The inclusion of the top open is an isomorphism of topological spaces.
  Apply functoriality of singular cochains along this isomorphism and pass to
  homology.
-/
theorem realSingularCohomology_topOpen_linearEquiv
    (X : TopCat.{v}) (n : ℕ) :
    Nonempty
      (SingularCohomology ℝ ((Opens.toTopCat X).obj (⊤ : Opens X)) n ≃ₗ[ℝ]
        RealSingularCohomology X n) := by
  let i : (Opens.toTopCat X).obj (⊤ : Opens X) ≅ X :=
    Opens.inclusionTopIso X
  let e :
      SingularCohomology ℝ ((Opens.toTopCat X).obj (⊤ : Opens X)) n ≅
        RealSingularCohomology X n :=
    { hom := HomologicalComplex.homologyMap (singularCochainMap ℝ i.inv) n
      inv := HomologicalComplex.homologyMap (singularCochainMap ℝ i.hom) n
      hom_inv_id := by
        rw [← HomologicalComplex.homologyMap_comp]
        rw [← singularCochainMap_comp (R := ℝ) i.hom i.inv]
        rw [i.hom_inv_id]
        rw [singularCochainMap_id]
        exact HomologicalComplex.homologyMap_id
          (K := SingularCochainComplex ℝ ((Opens.toTopCat X).obj (⊤ : Opens X))) (i := n)
      inv_hom_id := by
        rw [← HomologicalComplex.homologyMap_comp]
        rw [← singularCochainMap_comp (R := ℝ) i.inv i.hom]
        rw [i.inv_hom_id]
        rw [singularCochainMap_id]
        exact HomologicalComplex.homologyMap_id
          (K := SingularCochainComplex ℝ X) (i := n) }
  exact ⟨e.toLinearEquiv⟩

/--
%%handwave
name:
  Forgetting real scalars preserves cochain-complex cohomology and scalars
statement:
  If a cochain complex of real vector spaces is regarded as a cochain complex
  of abelian groups, its cohomology is additively the underlying abelian
  group of the original real cohomology, and this identification carries the
  homology map induced by scalar multiplication to scalar multiplication on
  cohomology.
proof:
  The forgetful functor from real vector spaces to abelian groups preserves
  kernels and cokernels, hence preserves homology of short complexes.  Apply
  the resulting homology isomorphism to the short complex computing
  cohomology in degree \(n\).  Naturality of this homology isomorphism for
  the scalar-multiplication natural transformation gives the scalar
  compatibility.
-/
theorem cochainComplex_forget₂_moduleCat_homology_addEquiv_with_smul
    (K : CochainComplex (ModuleCat.{v} ℝ) ℕ) :
    ∀ n : ℕ,
      ∃ e :
        ↥((((forget₂ (ModuleCat.{v} ℝ) AddCommGrpCat.{v}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K).homology n) ≃+
          ↥(K.homology n),
        ∀ (r : ℝ)
          (x :
            ↥((((forget₂ (ModuleCat.{v} ℝ) AddCommGrpCat.{v}).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj K).homology n)),
          e ((HomologicalComplex.homologyMap
                ((NatTrans.mapHomologicalComplex
                  ((ModuleCat.smulNatTrans ℝ) r) (ComplexShape.up ℕ)).app K) n) x) =
            r • e x := by
  intro n
  let F : ModuleCat.{v} ℝ ⥤ AddCommGrpCat.{v} :=
    forget₂ (ModuleCat.{v} ℝ) AddCommGrpCat.{v}
  let eIso :
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n) ≅
        F.obj (K.homology n) := by
    simpa [F] using (K.sc n).mapHomologyIso F
  refine ⟨eIso.addCommGroupIsoToAddEquiv, ?_⟩
  intro r x
  let τ : F ⟶ F := (ModuleCat.smulNatTrans ℝ) r
  have hτ :
      τ.app ((K.sc n).homology) =
        ((K.sc n).mapHomologyIso F).inv ≫
          ShortComplex.homologyMap ((K.sc n).mapNatTrans τ) ≫
          ((K.sc n).mapHomologyIso F).hom := by
    simpa [τ, F] using
      (CategoryTheory.NatTrans.app_homology
        (τ := τ) (S := K.sc n))
  have hcomm :
      ShortComplex.homologyMap ((K.sc n).mapNatTrans τ) ≫
          ((K.sc n).mapHomologyIso F).hom =
        ((K.sc n).mapHomologyIso F).hom ≫ τ.app ((K.sc n).homology) := by
    rw [hτ]
    simp
  have happ := ConcreteCategory.congr_hom hcomm x
  simpa [eIso, τ, F, ModuleCat.smulNatTrans] using happ

/--
%%handwave
name:
  Top-open singular cochains map to global sheafified cochains
statement:
  The sheafification unit gives a cochain map from ordinary singular cochains
  on the whole space, viewed as the top open subset, to global sections of
  the sheafified singular-cochain complex.
proof:
  In each degree, apply the sheafification unit on the top open set and then
  identify sections over the terminal open set with global sections.  The
  cochain-map identity is naturality of the sheafification unit with respect
  to the singular coboundary.
-/
noncomputable def openSingularCochainTopToSheafifiedGlobalSections
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    (realSingularCochainOpenComplexFunctor X).obj (op (⊤ : Opens X)) ⟶
      ((Sheaf.Γ (Opens.grothendieckTopology X)
        AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (realSingularCochainSheafComplex X) where
  f n := by
    let J := Opens.grothendieckTopology X
    letI : OrderTop (Opens X) :=
      { top := (⊤ : Opens X)
        le_top := fun _ => by
          intro _ _
          trivial }
    have hTop : IsTerminal (⊤ : Opens X) := by
      exact CategoryTheory.Limits.isTerminalTop
    let γ : Sheaf.Γ J AddCommGrpCat.{v} ≅
        (CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
          (op (⊤ : Opens X)) :=
      CategoryTheory.Sheaf.ΓNatIsoSheafSections
        (J := J) (A := AddCommGrpCat.{v})
        (T := (⊤ : Opens X)) hTop
    refine
      (CategoryTheory.toSheafify J
        ((realSingularCochainOpenPresheafComplex X).X n)).app
          (op (⊤ : Opens X)) ≫ ?_
    change
      (CategoryTheory.sheafify J
        ((realSingularCochainOpenPresheafComplex X).X n)).obj
          (op (⊤ : Opens X)) ⟶
        (((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (realSingularCochainSheafComplex X)).X n
    simpa [CategoryTheory.sheafSections, CategoryTheory.sheafify,
      realSingularCochainSheafComplex, J] using
        (γ.app ((realSingularCochainSheafComplex X).X n)).inv
  comm' n m hnm := by
    let J := Opens.grothendieckTopology X
    letI : OrderTop (Opens X) :=
      { top := (⊤ : Opens X)
        le_top := fun _ => by
          intro _ _
          trivial }
    have hTop : IsTerminal (⊤ : Opens X) := by
      exact CategoryTheory.Limits.isTerminalTop
    let γ : Sheaf.Γ J AddCommGrpCat.{v} ≅
        (CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
          (op (⊤ : Opens X)) :=
      CategoryTheory.Sheaf.ΓNatIsoSheafSections
        (J := J) (A := AddCommGrpCat.{v})
        (T := (⊤ : Opens X)) hTop
    change
      ((CategoryTheory.toSheafify J
        ((realSingularCochainOpenPresheafComplex X).X n)).app
          (op (⊤ : Opens X)) ≫
        (γ.app ((realSingularCochainSheafComplex X).X n)).inv) ≫
          (Sheaf.Γ J AddCommGrpCat.{v}).map
            ((realSingularCochainSheafComplex X).d n m) =
        ((realSingularCochainOpenPresheafComplex X).d n m).app
            (op (⊤ : Opens X)) ≫
          ((CategoryTheory.toSheafify J
            ((realSingularCochainOpenPresheafComplex X).X m)).app
              (op (⊤ : Opens X)) ≫
            (γ.app ((realSingularCochainSheafComplex X).X m)).inv)
    have hunit :=
      congr_app
        (CategoryTheory.toSheafify_naturality
          (J := J)
          (η := (realSingularCochainOpenPresheafComplex X).d n m))
        (op (⊤ : Opens X))
    have hγ :
        (γ.app ((realSingularCochainSheafComplex X).X n)).inv ≫
            (Sheaf.Γ J AddCommGrpCat.{v}).map
              ((realSingularCochainSheafComplex X).d n m) =
          ((CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
              (op (⊤ : Opens X))).map
              ((realSingularCochainSheafComplex X).d n m) ≫
            (γ.app ((realSingularCochainSheafComplex X).X m)).inv := by
      simpa using
        (γ.inv.naturality
          ((realSingularCochainSheafComplex X).d n m)).symm
    have hunit' :
        ((realSingularCochainOpenPresheafComplex X).d n m).app
              (op (⊤ : Opens X)) ≫
            (CategoryTheory.toSheafify J
              ((realSingularCochainOpenPresheafComplex X).X m)).app
              (op (⊤ : Opens X)) =
          (CategoryTheory.toSheafify J
              ((realSingularCochainOpenPresheafComplex X).X n)).app
              (op (⊤ : Opens X)) ≫
            ((CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
              (op (⊤ : Opens X))).map
              ((realSingularCochainSheafComplex X).d n m) := by
      change
        (((realSingularCochainOpenPresheafComplex X).d n m ≫
            CategoryTheory.toSheafify J
              ((realSingularCochainOpenPresheafComplex X).X m)).app
            (op (⊤ : Opens X))) =
          ((CategoryTheory.toSheafify J
              ((realSingularCochainOpenPresheafComplex X).X n) ≫
            CategoryTheory.sheafifyMap J
              ((realSingularCochainOpenPresheafComplex X).d n m)).app
            (op (⊤ : Opens X)))
      exact hunit
    calc
      ((CategoryTheory.toSheafify J
        ((realSingularCochainOpenPresheafComplex X).X n)).app
          (op (⊤ : Opens X)) ≫
        (γ.app ((realSingularCochainSheafComplex X).X n)).inv) ≫
          (Sheaf.Γ J AddCommGrpCat.{v}).map
            ((realSingularCochainSheafComplex X).d n m)
          =
        (CategoryTheory.toSheafify J
          ((realSingularCochainOpenPresheafComplex X).X n)).app
            (op (⊤ : Opens X)) ≫
          ((γ.app ((realSingularCochainSheafComplex X).X n)).inv ≫
            (Sheaf.Γ J AddCommGrpCat.{v}).map
              ((realSingularCochainSheafComplex X).d n m)) := by
            rw [Category.assoc]
      _ =
        (CategoryTheory.toSheafify J
          ((realSingularCochainOpenPresheafComplex X).X n)).app
            (op (⊤ : Opens X)) ≫
          (((CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
              (op (⊤ : Opens X))).map
              ((realSingularCochainSheafComplex X).d n m) ≫
            (γ.app ((realSingularCochainSheafComplex X).X m)).inv) := by
            exact
              congrArg
                (fun q =>
                  (CategoryTheory.toSheafify J
                    ((realSingularCochainOpenPresheafComplex X).X n)).app
                      (op (⊤ : Opens X)) ≫ q)
                hγ
      _ =
        ((CategoryTheory.toSheafify J
          ((realSingularCochainOpenPresheafComplex X).X n)).app
            (op (⊤ : Opens X)) ≫
          ((CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
              (op (⊤ : Opens X))).map
              ((realSingularCochainSheafComplex X).d n m)) ≫
            (γ.app ((realSingularCochainSheafComplex X).X m)).inv := by
            rw [← Category.assoc]
      _ =
        (((realSingularCochainOpenPresheafComplex X).d n m).app
              (op (⊤ : Opens X)) ≫
            (CategoryTheory.toSheafify J
              ((realSingularCochainOpenPresheafComplex X).X m)).app
              (op (⊤ : Opens X))) ≫
            (γ.app ((realSingularCochainSheafComplex X).X m)).inv := by
            exact
              congrArg
                (fun q => q ≫
                  (γ.app ((realSingularCochainSheafComplex X).X m)).inv)
                hunit'.symm
      _ =
        ((realSingularCochainOpenPresheafComplex X).d n m).app
            (op (⊤ : Opens X)) ≫
            ((CategoryTheory.toSheafify J
            ((realSingularCochainOpenPresheafComplex X).X m)).app
              (op (⊤ : Opens X)) ≫
            (γ.app ((realSingularCochainSheafComplex X).X m)).inv) := by
            rfl

/--
%%handwave
name:
  A sheafification-zero top-open cochain maps to zero globally
statement:
  If the top-open sheafification of an ordinary singular cochain is zero,
  then its image under the global top-open comparison map is zero.
proof:
  The comparison map is the sheafification unit followed by the isomorphism
  from terminal-open sections to global sections.
-/
theorem openSingularCochainTopToSheafifiedGlobalSections_f_eq_zero_of_toSheafify_eq_zero
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (n : ℕ)
    (α :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).X n)
    (hα :
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).X n)).app
          (op (⊤ : Opens X))) α = 0) :
    ((openSingularCochainTopToSheafifiedGlobalSections X).f n) α = 0 := by
  let J := Opens.grothendieckTopology X
  letI : OrderTop (Opens X) :=
    { top := (⊤ : Opens X)
      le_top := fun _ => by
        intro _ _
        trivial }
  have hTop : IsTerminal (⊤ : Opens X) := by
    exact CategoryTheory.Limits.isTerminalTop
  let γ : Sheaf.Γ J AddCommGrpCat.{v} ≅
      (CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
        (op (⊤ : Opens X)) :=
    CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (J := J) (A := AddCommGrpCat.{v})
      (T := (⊤ : Opens X)) hTop
  let F := (realSingularCochainSheafComplex X).X n
  change
    (ConcreteCategory.hom
      ((CategoryTheory.toSheafify J
        ((realSingularCochainOpenPresheafComplex X).X n)).app
          (op (⊤ : Opens X)) ≫ (γ.app F).inv)) α = 0
  rw [ConcreteCategory.comp_apply, hα]
  exact (γ.app F).inv.hom.map_zero

/--
%%handwave
name:
  A globally zero comparison image has zero top-open sheafification
statement:
  If an ordinary singular cochain maps to zero under the global top-open
  comparison map, then its top-open sheafification is zero.
proof:
  Apply the inverse terminal-open/global-sections isomorphism to the zero
  comparison image and cancel the isomorphism.
-/
theorem openSingularCochainTopToSheafifiedGlobalSections_toSheafify_eq_zero_of_f_eq_zero
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (n : ℕ)
    (α :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).X n)
    (hα : ((openSingularCochainTopToSheafifiedGlobalSections X).f n) α = 0) :
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).X n)).app
          (op (⊤ : Opens X))) α = 0 := by
  let J := Opens.grothendieckTopology X
  letI : OrderTop (Opens X) :=
    { top := (⊤ : Opens X)
      le_top := fun _ => by
        intro _ _
        trivial }
  have hTop : IsTerminal (⊤ : Opens X) := by
    exact CategoryTheory.Limits.isTerminalTop
  let γ : Sheaf.Γ J AddCommGrpCat.{v} ≅
      (CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
        (op (⊤ : Opens X)) :=
    CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (J := J) (A := AddCommGrpCat.{v})
      (T := (⊤ : Opens X)) hTop
  let F := (realSingularCochainSheafComplex X).X n
  let ηα :=
    ((CategoryTheory.toSheafify J
      ((realSingularCochainOpenPresheafComplex X).X n)).app
        (op (⊤ : Opens X))) α
  have hcomp :
      (ConcreteCategory.hom (γ.app F).inv) ηα = 0 := by
    simpa [openSingularCochainTopToSheafifiedGlobalSections, J, γ, F, ηα]
      using hα
  have hcancel :=
    congrArg (fun y => (ConcreteCategory.hom (γ.app F).hom) y) hcomp
  have hleft :
      (ConcreteCategory.hom (γ.app F).hom)
        ((ConcreteCategory.hom (γ.app F).inv) ηα) = ηα := by
    simpa using
      congrArg (fun f => (ConcreteCategory.hom f) ηα)
        (CategoryTheory.Iso.inv_hom_id (γ.app F))
  change ηα = 0
  calc
    ηα =
        (ConcreteCategory.hom (γ.app F).hom)
          ((ConcreteCategory.hom (γ.app F).inv) ηα) := hleft.symm
    _ = (ConcreteCategory.hom (γ.app F).hom) 0 := hcancel
    _ = 0 := (γ.app F).hom.hom.map_zero

/--
%%handwave
name:
  The top-open sheafification-unit cochain map commutes with scalar multiplication
statement:
  The cochain map from top-open singular cochains to global sheafified
  cochains commutes with multiplication by any real scalar.
proof:
  In each degree this is the naturality square of the sheafification unit for
  scalar multiplication, followed by naturality of the identification between
  global sections and sections over the terminal open set.
-/
theorem openSingularCochainTopToSheafifiedGlobalSections_scalar
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (r : ℝ) :
    openSingularCochainTopToSheafifiedGlobalSections X ≫
      (((Sheaf.Γ (Opens.grothendieckTopology X)
        AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
          (sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r)) =
    (realSingularCochainOpenComplexFunctorScalarNatTrans X r).app
        (op (⊤ : Opens X)) ≫
      openSingularCochainTopToSheafifiedGlobalSections X := by
  apply HomologicalComplex.hom_ext
  intro n
  let J := Opens.grothendieckTopology X
  letI : OrderTop (Opens X) :=
    { top := (⊤ : Opens X)
      le_top := fun _ => by
        intro _ _
        trivial }
  have hTop : IsTerminal (⊤ : Opens X) := by
    exact CategoryTheory.Limits.isTerminalTop
  let γ : Sheaf.Γ J AddCommGrpCat.{v} ≅
      (CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
        (op (⊤ : Opens X)) :=
    CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (J := J) (A := AddCommGrpCat.{v})
      (T := (⊤ : Opens X)) hTop
  change
    ((CategoryTheory.toSheafify J
      ((realSingularCochainOpenPresheafComplex X).X n)).app
        (op (⊤ : Opens X)) ≫
      (γ.app ((realSingularCochainSheafComplex X).X n)).inv) ≫
        (Sheaf.Γ J AddCommGrpCat.{v}).map
          ((sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r).f n) =
      ((realSingularCochainOpenPresheafComplexScalarEnd X r).f n).app
          (op (⊤ : Opens X)) ≫
        ((CategoryTheory.toSheafify J
          ((realSingularCochainOpenPresheafComplex X).X n)).app
            (op (⊤ : Opens X)) ≫
          (γ.app ((realSingularCochainSheafComplex X).X n)).inv)
  have hunit :=
    congr_app
      (CategoryTheory.toSheafify_naturality
        (J := J)
        (η := (realSingularCochainOpenPresheafComplexScalarEnd X r).f n))
      (op (⊤ : Opens X))
  have hγ :
      (γ.app ((realSingularCochainSheafComplex X).X n)).inv ≫
          (Sheaf.Γ J AddCommGrpCat.{v}).map
            ((sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r).f n) =
        ((CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
            (op (⊤ : Opens X))).map
            ((sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r).f n) ≫
          (γ.app ((realSingularCochainSheafComplex X).X n)).inv := by
    simpa using
      (γ.inv.naturality
        ((sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r).f n)).symm
  have hunit' :
      ((realSingularCochainOpenPresheafComplexScalarEnd X r).f n).app
            (op (⊤ : Opens X)) ≫
          (CategoryTheory.toSheafify J
            ((realSingularCochainOpenPresheafComplex X).X n)).app
            (op (⊤ : Opens X)) =
        (CategoryTheory.toSheafify J
            ((realSingularCochainOpenPresheafComplex X).X n)).app
            (op (⊤ : Opens X)) ≫
          ((CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
            (op (⊤ : Opens X))).map
            ((sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r).f n) := by
    change
      ((((realSingularCochainOpenPresheafComplexScalarEnd X r).f n) ≫
          CategoryTheory.toSheafify J
            ((realSingularCochainOpenPresheafComplex X).X n)).app
          (op (⊤ : Opens X))) =
        ((CategoryTheory.toSheafify J
            ((realSingularCochainOpenPresheafComplex X).X n) ≫
          CategoryTheory.sheafifyMap J
            ((realSingularCochainOpenPresheafComplexScalarEnd X r).f n)).app
          (op (⊤ : Opens X)))
    exact hunit
  calc
    ((CategoryTheory.toSheafify J
      ((realSingularCochainOpenPresheafComplex X).X n)).app
        (op (⊤ : Opens X)) ≫
      (γ.app ((realSingularCochainSheafComplex X).X n)).inv) ≫
        (Sheaf.Γ J AddCommGrpCat.{v}).map
          ((sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r).f n)
        =
      (CategoryTheory.toSheafify J
        ((realSingularCochainOpenPresheafComplex X).X n)).app
          (op (⊤ : Opens X)) ≫
        ((γ.app ((realSingularCochainSheafComplex X).X n)).inv ≫
          (Sheaf.Γ J AddCommGrpCat.{v}).map
            ((sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r).f n)) := by
          rw [Category.assoc]
    _ =
      (CategoryTheory.toSheafify J
        ((realSingularCochainOpenPresheafComplex X).X n)).app
          (op (⊤ : Opens X)) ≫
        (((CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
            (op (⊤ : Opens X))).map
            ((sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r).f n) ≫
          (γ.app ((realSingularCochainSheafComplex X).X n)).inv) := by
          exact
            congrArg
              (fun q =>
                (CategoryTheory.toSheafify J
                  ((realSingularCochainOpenPresheafComplex X).X n)).app
                    (op (⊤ : Opens X)) ≫ q)
              hγ
    _ =
      ((CategoryTheory.toSheafify J
        ((realSingularCochainOpenPresheafComplex X).X n)).app
          (op (⊤ : Opens X)) ≫
        ((CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
            (op (⊤ : Opens X))).map
            ((sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r).f n)) ≫
          (γ.app ((realSingularCochainSheafComplex X).X n)).inv := by
          rw [← Category.assoc]
    _ =
      (((realSingularCochainOpenPresheafComplexScalarEnd X r).f n).app
            (op (⊤ : Opens X)) ≫
          (CategoryTheory.toSheafify J
            ((realSingularCochainOpenPresheafComplex X).X n)).app
            (op (⊤ : Opens X))) ≫
          (γ.app ((realSingularCochainSheafComplex X).X n)).inv := by
          exact
            congrArg
              (fun q => q ≫
                (γ.app ((realSingularCochainSheafComplex X).X n)).inv)
              hunit'.symm
    _ =
      ((realSingularCochainOpenPresheafComplexScalarEnd X r).f n).app
          (op (⊤ : Opens X)) ≫
        ((CategoryTheory.toSheafify J
          ((realSingularCochainOpenPresheafComplex X).X n)).app
            (op (⊤ : Opens X)) ≫
          (γ.app ((realSingularCochainSheafComplex X).X n)).inv) := by
          rfl

/--
%%handwave
name:
  Restriction of a top-open singular cochain cycle to an open subset
statement:
  A singular cochain cycle on the whole space restricts to a singular cochain
  cycle on any open subset.
proof:
  Apply the cycle map induced by the restriction cochain map
  \(C^\bullet(X;\mathbb R)\to C^\bullet(U;\mathbb R)\).
-/
noncomputable def openSingularCochainTopRestrictCycle
    (X : TopCat.{v}) (U : Opens X) (n : ℕ) :
    ((realSingularCochainOpenComplexFunctor X).obj
      (op (⊤ : Opens X))).cycles n ⟶
    ((realSingularCochainOpenComplexFunctor X).obj
      (op U)).cycles n :=
  HomologicalComplex.cyclesMap
    ((realSingularCochainOpenComplexFunctor X).map
      (homOfLE (show U ≤ (⊤ : Opens X) from by
        intro x _hx
        trivial)).op) n

/--
%%handwave
name:
  A covering sieve of an open contains a neighborhood of each point
statement:
  If a sieve on an open subset is covering for the usual topology on opens,
  then every point of the open lies in a smaller open whose inclusion belongs
  to the sieve.
proof:
  Interpret the sieve as a presieve and use the standard description of the
  Grothendieck topology on open subsets: the opens appearing in a covering
  presieve have supremum equal to the original open.
-/
theorem opens_coveringSieve_exists_mem_of_mem
    (X : TopCat.{v}) {U : Opens X} (S : Sieve U)
    (hS : S ∈ Opens.grothendieckTopology X U)
    {x : X} (hxU : x ∈ U) :
    ∃ (V : Opens X) (i : V ⟶ U), S i ∧ x ∈ V := by
  have hgen :
      Sieve.generate S.1 ∈ Opens.grothendieckTopology X U := by
    simpa [Sieve.generate_sieve] using hS
  have hsup :=
    TopCat.Presheaf.coveringOfPresieve.iSup_eq_of_mem_grothendieck
      (X := X) U S.1 hgen
  have hx :
      x ∈ iSup (TopCat.Presheaf.coveringOfPresieve U S.1) := by
    simpa [hsup] using hxU
  rcases Opens.mem_iSup.mp hx with ⟨a, hxa⟩
  rcases a with ⟨V, i, hiS⟩
  exact ⟨V, i, hiS, hxa⟩

/--
%%handwave
name:
  Sheafification of abelian presheaves is locally injective
statement:
  For an abelian-group presheaf on a topological space, the canonical map to
  its sheafification is locally injective.
proof:
  This is the locally injective half of the standard locally bijective
  universal map from a presheaf to its sheafification.
-/
theorem addCommGrp_toSheafify_isLocallyInjective
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (P : TopCat.Presheaf AddCommGrpCat.{v} X) :
    CategoryTheory.Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) := by
  infer_instance

/--
%%handwave
name:
  A section that sheafifies to zero is locally zero
statement:
  If a section of an abelian-group presheaf maps to zero in the sheafification,
  then every point has a smaller open neighborhood on which the original
  section restricts to zero.
proof:
  The sheafification unit is locally injective.  Apply local injectivity to
  the section and the zero section, then use the description of covering
  sieves on open subsets to choose a neighborhood of the given point.
-/
theorem addCommGrp_toSheafify_eq_zero_locally
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (P : TopCat.Presheaf AddCommGrpCat.{v} X)
    {U : Opens X} (s : P.obj (op U))
    (hs :
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X) P).app (op U)) s = 0) :
    ∀ x : X, x ∈ U →
      ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        P.map (homOfLE hVU).op s = 0 := by
  intro x hxU
  let J := Opens.grothendieckTopology X
  let η := CategoryTheory.toSheafify J P
  let S : Sieve U := CategoryTheory.Presheaf.equalizerSieve s 0
  have hS : S ∈ J U := by
    exact
      CategoryTheory.Presheaf.equalizerSieve_mem
        J η s 0 (by simpa [η] using hs)
  rcases opens_coveringSieve_exists_mem_of_mem X S hS hxU with
    ⟨V, i, hiS, hxV⟩
  refine ⟨V, leOfHom i, hxV, ?_⟩
  have hiS' : P.map i.op s = P.map i.op 0 := hiS
  simpa using hiS'

/--
%%handwave
name:
  A sheafified section is locally represented before sheafification
statement:
  Every section of the sheafification of an abelian-group presheaf is locally
  represented by a section of the original presheaf.
proof:
  The sheafification unit is locally surjective.  Apply the image-sieve
  description of local surjectivity and then use the description of covering
  sieves on open subsets to choose a neighborhood of the given point.
-/
theorem addCommGrp_toSheafify_locally_represented
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (P : TopCat.Presheaf AddCommGrpCat.{v} X)
    {U : Opens X}
    (s :
      (CategoryTheory.sheafify (Opens.grothendieckTopology X) P).obj
        (op U)) :
    ∀ x : X, x ∈ U →
      ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        ∃ t : P.obj (op V),
          ((CategoryTheory.toSheafify
            (Opens.grothendieckTopology X) P).app (op V)) t =
            (CategoryTheory.sheafify
              (Opens.grothendieckTopology X) P).map
                (homOfLE hVU).op s := by
  intro x hxU
  let J := Opens.grothendieckTopology X
  let η := CategoryTheory.toSheafify J P
  let S : Sieve U := CategoryTheory.Presheaf.imageSieve η s
  have hS : S ∈ J U := by
    exact CategoryTheory.Presheaf.imageSieve_mem J η s
  rcases opens_coveringSieve_exists_mem_of_mem X S hS hxU with
    ⟨V, i, hiS, hxV⟩
  refine ⟨V, leOfHom i, hxV, ?_⟩
  rcases hiS with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  simpa [S, J, η, Subsingleton.elim i (homOfLE (leOfHom i))] using ht

/--
%%handwave
name:
  A top-open sheafified section is locally represented before sheafification
statement:
  Every section of the sheafification over the whole space is locally
  represented by a section of the original presheaf.
proof:
  Apply local representability of sheafified sections to the terminal open
  subset and forget the automatic inclusion into the terminal open.
-/
theorem addCommGrp_toSheafify_top_locally_represented
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (P : TopCat.Presheaf AddCommGrpCat.{v} X)
    (s :
      (CategoryTheory.sheafify (Opens.grothendieckTopology X) P).obj
        (op (⊤ : Opens X))) :
    ∀ x : X,
      ∃ (U : Opens X), x ∈ U ∧
        ∃ t : P.obj (op U),
          ((CategoryTheory.toSheafify
            (Opens.grothendieckTopology X) P).app (op U)) t =
            (CategoryTheory.sheafify
              (Opens.grothendieckTopology X) P).map
                (homOfLE (show U ≤ (⊤ : Opens X) from by
                  intro y _hy
                  trivial)).op s := by
  intro x
  rcases
    addCommGrp_toSheafify_locally_represented
      (X := X) P (U := (⊤ : Opens X)) s x (by trivial) with
    ⟨U, hUtop, hxU, t, ht⟩
  refine ⟨U, hxU, t, ?_⟩
  simpa [Subsingleton.elim (homOfLE hUtop)
      (homOfLE (show U ≤ (⊤ : Opens X) from by
        intro y _hy
        trivial))] using ht

/--
%%handwave
name:
  Local vanishing of a top-open singular cochain cycle
statement:
  A singular cochain cycle on the whole space has locally zero cohomology
  class if every point has an open neighborhood on which the restricted cycle
  has zero singular cohomology class.
proof:
  This is a definition of the standard local vanishing condition.
-/
def openSingularCochainTopCycleLocallyZero
    (X : TopCat.{v}) (n : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles n) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧
    (((realSingularCochainOpenComplexFunctor X).obj
      (op U)).homologyπ n)
      ((openSingularCochainTopRestrictCycle X U n) z) = 0

/--
%%handwave
name:
  Local vanishing as restricted degree-zero cycles
statement:
  A singular zero-cochain cycle on the whole space vanishes locally as a
  cycle if every point has an open neighborhood on which the restricted
  zero-cycle is zero.
proof:
  This records the pointwise local vanishing condition before passing to
  degree-zero cohomology.
-/
def openSingularCochainTopCycleLocallyZeroAsCycle
    (X : TopCat.{v})
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles 0) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧
    (openSingularCochainTopRestrictCycle X U 0) z = 0

/--
%%handwave
name:
  Local zero degree-zero cohomology means local zero restricted cycles
statement:
  If a singular zero-cochain cycle on the whole space has locally zero
  degree-zero singular cohomology class, then it vanishes locally as a
  restricted zero-cycle.
proof:
  On each local open set, degree-zero cycles map isomorphically to
  degree-zero cohomology because there is no incoming differential.
-/
theorem openSingularCochainTopCycleLocallyZeroAsCycle_of_cycleLocallyZero
    (X : TopCat.{v})
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles 0)
    (hz : openSingularCochainTopCycleLocallyZero X 0 z) :
    openSingularCochainTopCycleLocallyZeroAsCycle X z := by
  intro x
  rcases hz x with ⟨U, hxU, hU⟩
  refine ⟨U, hxU, ?_⟩
  exact
    cochainComplex_addCommGrp_cycle_zero_of_homologyπ_zero_eq_zero
      (K := (realSingularCochainOpenComplexFunctor X).obj (op U))
      ((openSingularCochainTopRestrictCycle X U 0) z)
      hU

/--
%%handwave
name:
  Local zero restricted degree-zero cycles have locally zero cohomology class
statement:
  If a singular zero-cochain cycle on the whole space vanishes locally as a
  restricted cycle, then it has locally zero degree-zero singular cohomology
  class.
proof:
  On each local open set the restricted cycle is zero, so its image in
  degree-zero cohomology is zero.
-/
theorem openSingularCochainTopCycleLocallyZero_of_cycleLocallyZeroAsCycle
    (X : TopCat.{v})
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles 0)
    (hz : openSingularCochainTopCycleLocallyZeroAsCycle X z) :
    openSingularCochainTopCycleLocallyZero X 0 z := by
  intro x
  rcases hz x with ⟨U, hxU, hU⟩
  refine ⟨U, hxU, ?_⟩
  rw [hU]
  exact map_zero _

/--
%%handwave
name:
  Positive-degree sheafified-zero cycles are locally zero
statement:
  If the sheafification of the underlying cochain of a positive-degree
  top-open singular cycle is zero, then the cycle has locally zero singular
  cohomology class.
proof:
  Since the sheafification unit is locally injective, the underlying cochain
  restricts to zero near every point.  Naturality of the cycle inclusion
  identifies this restriction with the underlying cochain of the restricted
  cycle, so the restricted cycle itself is zero and hence has zero local
  cohomology class.
-/
theorem openSingularCochainTopCycleLocallyZero_succ_of_toSheafify_iCycles_eq_zero
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (m : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles (m + 1))
    (hz :
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).X (m + 1))).app
          (op (⊤ : Opens X)))
        ((((realSingularCochainOpenComplexFunctor X).obj
          (op (⊤ : Opens X))).iCycles (m + 1)) z) = 0) :
    openSingularCochainTopCycleLocallyZero X (m + 1) z := by
  intro x
  rcases
    addCommGrp_toSheafify_eq_zero_locally
      (X := X) ((realSingularCochainOpenPresheafComplex X).X (m + 1))
      (U := (⊤ : Opens X))
      ((((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).iCycles (m + 1)) z)
      hz x (by trivial) with
    ⟨U, hUtop, hxU, hres⟩
  refine ⟨U, hxU, ?_⟩
  have hzU : (openSingularCochainTopRestrictCycle X U (m + 1)) z = 0 := by
    apply
      (AddCommGrpCat.mono_iff_injective
        (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))).1
        inferInstance
    have hcycle_i :
        (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
            ((openSingularCochainTopRestrictCycle X U (m + 1)) z) =
          (((realSingularCochainOpenComplexFunctor X).map
            (homOfLE hUtop).op).f (m + 1))
            ((((realSingularCochainOpenComplexFunctor X).obj
              (op (⊤ : Opens X))).iCycles (m + 1)) z) := by
      change
        (ConcreteCategory.hom
          (openSingularCochainTopRestrictCycle X U (m + 1) ≫
            ((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))) z =
        (ConcreteCategory.hom
          (((realSingularCochainOpenComplexFunctor X).obj
              (op (⊤ : Opens X))).iCycles (m + 1) ≫
            ((realSingularCochainOpenComplexFunctor X).map
              (homOfLE hUtop).op).f (m + 1))) z
      have hmorph :
          openSingularCochainTopRestrictCycle X U (m + 1) ≫
              ((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1) =
            ((realSingularCochainOpenComplexFunctor X).obj
                (op (⊤ : Opens X))).iCycles (m + 1) ≫
              ((realSingularCochainOpenComplexFunctor X).map
                (homOfLE hUtop).op).f (m + 1) := by
        simpa [openSingularCochainTopRestrictCycle] using
          (HomologicalComplex.cyclesMap_i
            (((realSingularCochainOpenComplexFunctor X).map
              (homOfLE hUtop).op)) (m + 1))
      exact congrArg (fun f => (ConcreteCategory.hom f) z) hmorph
    have hres' :
        (((realSingularCochainOpenComplexFunctor X).map
            (homOfLE hUtop).op).f (m + 1))
            ((((realSingularCochainOpenComplexFunctor X).obj
              (op (⊤ : Opens X))).iCycles (m + 1)) z) = 0 := by
      simpa [realSingularCochainOpenPresheafComplex] using hres
    calc
      (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
          ((openSingularCochainTopRestrictCycle X U (m + 1)) z)
          =
        (((realSingularCochainOpenComplexFunctor X).map
          (homOfLE hUtop).op).f (m + 1))
          ((((realSingularCochainOpenComplexFunctor X).obj
            (op (⊤ : Opens X))).iCycles (m + 1)) z) := hcycle_i
      _ = 0 := hres'
      _ =
        (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
          (0 : ((realSingularCochainOpenComplexFunctor X).obj (op U)).cycles (m + 1)) := by
          exact
            (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles
              (m + 1)).hom.map_zero.symm
  rw [hzU]
  exact map_zero _

/--
%%handwave
name:
  A zero positive sheafified top-open class has a global sheafified primitive
statement:
  If the image of a top-open singular \((m+1)\)-cochain cycle has zero
  cohomology class in the global sections of the sheafified cochain complex,
  then it is the coboundary of a global sheafified \(m\)-cochain.
proof:
  Apply [a zero positive cohomology class in an abelian cochain complex has a primitive](lean:JJMath.Cohomology.cochainComplex_addCommGrp_exists_preimage_of_homologyπ_eq_zero) to the global-sections cochain complex.
-/
theorem openSingularCochainTopToSheafifiedGlobalSections_exists_primitive_succ_of_homologyπ_eq_zero
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (m : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles (m + 1))
    (hz :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).homologyπ (m + 1))
        ((HomologicalComplex.cyclesMap
          (openSingularCochainTopToSheafifiedGlobalSections X) (m + 1)) z) = 0) :
    ∃ β :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).X m),
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).d m (m + 1)) β =
        ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).iCycles (m + 1))
          ((HomologicalComplex.cyclesMap
            (openSingularCochainTopToSheafifiedGlobalSections X) (m + 1)) z) := by
  let L :=
    (((Sheaf.Γ (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
      (realSingularCochainSheafComplex X))
  exact
    cochainComplex_addCommGrp_exists_preimage_of_homologyπ_eq_zero
      (K := L) m
      ((HomologicalComplex.cyclesMap
        (openSingularCochainTopToSheafifiedGlobalSections X) (m + 1)) z)
      hz

/--
%%handwave
name:
  Local boundary representatives for a positive-degree top-open singular cycle
statement:
  A singular \((m+1)\)-cochain cycle on the whole space is locally a
  coboundary if every point has an open neighborhood on which the restricted
  cycle is the coboundary of an \(m\)-cochain.
proof:
  This is the local primitive condition used by the subdivision argument.
-/
def openSingularCochainTopCycleLocallyBoundary
    (X : TopCat.{v}) (m : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles (m + 1)) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧
    ∃ β : ((realSingularCochainOpenComplexFunctor X).obj (op U)).X m,
      (((realSingularCochainOpenComplexFunctor X).obj (op U)).d m (m + 1)) β =
        (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
          ((openSingularCochainTopRestrictCycle X U (m + 1)) z)

/--
%%handwave
name:
  Local sheafified boundary representatives for a positive-degree top-open singular cycle
statement:
  A singular \((m+1)\)-cochain cycle on the whole space is locally a
  sheafified coboundary if every point has an open neighborhood and an
  \(m\)-cochain whose coboundary agrees with the restricted cycle after
  applying the sheafification map.
proof:
  This records the local equality before applying local injectivity of
  sheafification.
-/
def openSingularCochainTopCycleLocallySheafifiedBoundary
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (m : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles (m + 1)) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧
    ∃ β : ((realSingularCochainOpenComplexFunctor X).obj (op U)).X m,
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).X (m + 1))).app
          (op U))
        ((((realSingularCochainOpenComplexFunctor X).obj (op U)).d m (m + 1)) β -
          (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
            ((openSingularCochainTopRestrictCycle X U (m + 1)) z)) = 0

/--
%%handwave
name:
  A top-open sheafified primitive gives local sheafified boundary representatives
statement:
  If a section over the whole space of the sheafified \(m\)-cochains has
  coboundary equal to the sheafification of a top-open \((m+1)\)-cycle, then
  the top-open cycle is locally a sheafified ordinary coboundary.
proof:
  Represent the sheafified primitive locally by an ordinary singular
  \(m\)-cochain.  Naturality of sheafification with respect to the
  coboundary identifies the sheafified coboundary of this representative
  with the restriction of the top-open sheafified coboundary.  Naturality of
  the cycle inclusion identifies the restricted top-open cycle with the
  cycle of the restricted cochain.
-/
theorem openSingularCochainTopCycleLocallySheafifiedBoundary_of_topOpenPrimitive
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (m : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles (m + 1))
    (βTop :
      (CategoryTheory.sheafify (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).X m)).obj
        (op (⊤ : Opens X)))
    (hβTop :
      ((CategoryTheory.sheafifyMap (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).d m (m + 1))).app
          (op (⊤ : Opens X))) βTop =
        ((CategoryTheory.toSheafify
          (Opens.grothendieckTopology X)
          ((realSingularCochainOpenPresheafComplex X).X (m + 1))).app
            (op (⊤ : Opens X)))
          ((((realSingularCochainOpenComplexFunctor X).obj
            (op (⊤ : Opens X))).iCycles (m + 1)) z)) :
    openSingularCochainTopCycleLocallySheafifiedBoundary X m z := by
  intro x
  let J := Opens.grothendieckTopology X
  let Pm : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X m
  let Pnp1 : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X (m + 1)
  let dmn : Pm ⟶ Pnp1 := (realSingularCochainOpenPresheafComplex X).d m (m + 1)
  rcases
    addCommGrp_toSheafify_top_locally_represented
      (X := X) Pm βTop x with
    ⟨U, hxU, βU, hβU⟩
  refine ⟨U, hxU, βU, ?_⟩
  have hUtop : U ≤ (⊤ : Opens X) := by
    intro y _hy
    trivial
  let ρTopU :=
    ((realSingularCochainOpenComplexFunctor X).map (homOfLE hUtop).op)
  have hη_d :
      ((CategoryTheory.toSheafify J Pnp1).app (op U))
          ((((realSingularCochainOpenComplexFunctor X).obj (op U)).d m (m + 1)) βU) =
        ((CategoryTheory.sheafifyMap J dmn).app (op U))
          (((CategoryTheory.toSheafify J Pm).app (op U)) βU) := by
    have hnat :
        dmn.app (op U) ≫ (CategoryTheory.toSheafify J Pnp1).app (op U) =
          (CategoryTheory.toSheafify J Pm).app (op U) ≫
            (CategoryTheory.sheafifyMap J dmn).app (op U) :=
      congr_app
        (CategoryTheory.toSheafify_naturality
          (J := J) (η := dmn)) (op U)
    have happ := congrArg (fun f => (ConcreteCategory.hom f) βU) hnat
    change
      (ConcreteCategory.hom
        (dmn.app (op U) ≫ (CategoryTheory.toSheafify J Pnp1).app (op U))) βU =
      (ConcreteCategory.hom
        ((CategoryTheory.toSheafify J Pm).app (op U) ≫
          (CategoryTheory.sheafifyMap J dmn).app (op U))) βU
    exact happ
  have hd_restrict :
      ((CategoryTheory.sheafifyMap J dmn).app (op U))
          ((CategoryTheory.sheafify J Pm).map (homOfLE hUtop).op βTop) =
        ((CategoryTheory.sheafify J Pnp1).map (homOfLE hUtop).op)
          (((CategoryTheory.sheafifyMap J dmn).app
            (op (⊤ : Opens X))) βTop) := by
    have hnat :=
      ((CategoryTheory.sheafifyMap J dmn).naturality
        (homOfLE hUtop).op)
    have happ := congrArg (fun f => (ConcreteCategory.hom f) βTop) hnat
    simp at happ ⊢
  have hη_dβ :
      ((CategoryTheory.toSheafify J Pnp1).app (op U))
          ((((realSingularCochainOpenComplexFunctor X).obj (op U)).d m (m + 1)) βU) =
        ((CategoryTheory.sheafify J Pnp1).map (homOfLE hUtop).op)
          (((CategoryTheory.toSheafify J Pnp1).app (op (⊤ : Opens X)))
            ((((realSingularCochainOpenComplexFunctor X).obj
              (op (⊤ : Opens X))).iCycles (m + 1)) z)) := by
    calc
      ((CategoryTheory.toSheafify J Pnp1).app (op U))
          ((((realSingularCochainOpenComplexFunctor X).obj (op U)).d m (m + 1)) βU)
          =
        ((CategoryTheory.sheafifyMap J dmn).app (op U))
          (((CategoryTheory.toSheafify J Pm).app (op U)) βU) := hη_d
      _ =
        ((CategoryTheory.sheafifyMap J dmn).app (op U))
          ((CategoryTheory.sheafify J Pm).map (homOfLE hUtop).op βTop) := by
          rw [hβU]
      _ =
        ((CategoryTheory.sheafify J Pnp1).map (homOfLE hUtop).op)
          (((CategoryTheory.sheafifyMap J dmn).app
            (op (⊤ : Opens X))) βTop) := hd_restrict
      _ =
        ((CategoryTheory.sheafify J Pnp1).map (homOfLE hUtop).op)
          (((CategoryTheory.toSheafify J Pnp1).app (op (⊤ : Opens X)))
            ((((realSingularCochainOpenComplexFunctor X).obj
              (op (⊤ : Opens X))).iCycles (m + 1)) z)) := by
          rw [hβTop]
  have hcycle_i :
      (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
          ((openSingularCochainTopRestrictCycle X U (m + 1)) z) =
        (ρTopU.f (m + 1))
          ((((realSingularCochainOpenComplexFunctor X).obj
            (op (⊤ : Opens X))).iCycles (m + 1)) z) := by
    change
      (ConcreteCategory.hom
        (openSingularCochainTopRestrictCycle X U (m + 1) ≫
          ((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))) z =
      (ConcreteCategory.hom
        (((realSingularCochainOpenComplexFunctor X).obj
            (op (⊤ : Opens X))).iCycles (m + 1) ≫
          ρTopU.f (m + 1))) z
    have hmorph :
        openSingularCochainTopRestrictCycle X U (m + 1) ≫
            ((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1) =
          ((realSingularCochainOpenComplexFunctor X).obj
              (op (⊤ : Opens X))).iCycles (m + 1) ≫
            ρTopU.f (m + 1) := by
      simpa [openSingularCochainTopRestrictCycle, ρTopU] using
        (HomologicalComplex.cyclesMap_i ρTopU (m + 1))
    exact congrArg (fun f => (ConcreteCategory.hom f) z) hmorph
  have hη_cycle :
      ((CategoryTheory.sheafify J Pnp1).map (homOfLE hUtop).op)
          (((CategoryTheory.toSheafify J Pnp1).app (op (⊤ : Opens X)))
            ((((realSingularCochainOpenComplexFunctor X).obj
              (op (⊤ : Opens X))).iCycles (m + 1)) z)) =
        ((CategoryTheory.toSheafify J Pnp1).app (op U))
          ((((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
            ((openSingularCochainTopRestrictCycle X U (m + 1)) z)) := by
    have hnat :=
      (CategoryTheory.toSheafify J Pnp1).naturality
        (homOfLE hUtop).op
    have happ :=
      congrArg
        (fun f => (ConcreteCategory.hom f)
          ((((realSingularCochainOpenComplexFunctor X).obj
            (op (⊤ : Opens X))).iCycles (m + 1)) z))
        hnat
    calc
      ((CategoryTheory.sheafify J Pnp1).map (homOfLE hUtop).op)
          (((CategoryTheory.toSheafify J Pnp1).app (op (⊤ : Opens X)))
            ((((realSingularCochainOpenComplexFunctor X).obj
              (op (⊤ : Opens X))).iCycles (m + 1)) z))
          =
        ((CategoryTheory.toSheafify J Pnp1).app (op U))
          ((ρTopU.f (m + 1))
            ((((realSingularCochainOpenComplexFunctor X).obj
              (op (⊤ : Opens X))).iCycles (m + 1)) z)) := by
          simpa [J, Pnp1, ρTopU, realSingularCochainOpenPresheafComplex,
            ConcreteCategory.comp_apply] using happ.symm
      _ =
        ((CategoryTheory.toSheafify J Pnp1).app (op U))
          ((((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
            ((openSingularCochainTopRestrictCycle X U (m + 1)) z)) := by
          rw [← hcycle_i]
  calc
    ((CategoryTheory.toSheafify J Pnp1).app (op U))
        ((((realSingularCochainOpenComplexFunctor X).obj (op U)).d m (m + 1)) βU -
          (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
            ((openSingularCochainTopRestrictCycle X U (m + 1)) z))
        =
      ((CategoryTheory.toSheafify J Pnp1).app (op U))
          ((((realSingularCochainOpenComplexFunctor X).obj (op U)).d m (m + 1)) βU) -
        ((CategoryTheory.toSheafify J Pnp1).app (op U))
          ((((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
            ((openSingularCochainTopRestrictCycle X U (m + 1)) z)) := by
        exact map_sub
          (ConcreteCategory.hom ((CategoryTheory.toSheafify J Pnp1).app (op U))) _ _
    _ = 0 := by
        rw [hη_dβ, hη_cycle, sub_self]

/--
%%handwave
name:
  A global-section sheafified primitive gives a terminal-open sheafified primitive
statement:
  If the sheafified image of a top-open singular \((m+1)\)-cochain cycle is
  the coboundary of a global sheafified \(m\)-cochain, then, after identifying
  global sections with sections over the terminal open set, there is a
  terminal-open sheafified \(m\)-cochain whose coboundary is the
  sheafification of the original top-open cycle.
proof:
  Use the standard isomorphism between global sections and sections over the
  terminal open set.  Naturality of this isomorphism transports the
  global-sections differential to the sheafified top-open differential, and
  naturality of cycle inclusions for the sheafification-unit cochain map
  identifies the transported cycle with the sheafification of the original
  top-open cycle.
-/
theorem openSingularCochainTop_exists_topOpenSheafifiedPrimitive_of_globalSectionsPrimitive
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (m : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles (m + 1))
    (β :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).X m))
    (hβ :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).d m (m + 1)) β =
        ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).iCycles (m + 1))
          ((HomologicalComplex.cyclesMap
            (openSingularCochainTopToSheafifiedGlobalSections X) (m + 1)) z)) :
    ∃ βTop :
      (CategoryTheory.sheafify (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).X m)).obj
        (op (⊤ : Opens X)),
      ((CategoryTheory.sheafifyMap (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).d m (m + 1))).app
          (op (⊤ : Opens X))) βTop =
        ((CategoryTheory.toSheafify
          (Opens.grothendieckTopology X)
          ((realSingularCochainOpenPresheafComplex X).X (m + 1))).app
            (op (⊤ : Opens X)))
          ((((realSingularCochainOpenComplexFunctor X).obj
            (op (⊤ : Opens X))).iCycles (m + 1)) z) := by
  let J := Opens.grothendieckTopology X
  letI : OrderTop (Opens X) :=
    { top := (⊤ : Opens X)
      le_top := fun _ => by
        intro _ _
        trivial }
  have hTop : IsTerminal (⊤ : Opens X) := by
    exact CategoryTheory.Limits.isTerminalTop
  let γ : Sheaf.Γ J AddCommGrpCat.{v} ≅
      (CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
        (op (⊤ : Opens X)) :=
      CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (J := J) (A := AddCommGrpCat.{v})
      (T := (⊤ : Opens X)) hTop
  let Pm : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X m
  let Pnp1 : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X (m + 1)
  let Fm := (realSingularCochainSheafComplex X).X m
  let Fnp1 := (realSingularCochainSheafComplex X).X (m + 1)
  let dmn : Pm ⟶ Pnp1 := (realSingularCochainOpenPresheafComplex X).d m (m + 1)
  let K := (realSingularCochainOpenComplexFunctor X).obj (op (⊤ : Opens X))
  let L :=
    (((Sheaf.Γ J AddCommGrpCat.{v}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
      (realSingularCochainSheafComplex X))
  let φ := openSingularCochainTopToSheafifiedGlobalSections X
  let βTop : (CategoryTheory.sheafify J Pm).obj (op (⊤ : Opens X)) := by
    simpa [J, Pm, Fm, realSingularCochainSheafComplex,
      CategoryTheory.sheafSections, CategoryTheory.sheafify] using
      (ConcreteCategory.hom (γ.app Fm).hom) β
  refine ⟨βTop, ?_⟩
  have htransport_d :
      (ConcreteCategory.hom (γ.app Fnp1).hom) ((L.d m (m + 1)) β) =
        ((CategoryTheory.sheafifyMap J dmn).app (op (⊤ : Opens X))) βTop := by
    have hnat :
        L.d m (m + 1) ≫ (γ.app Fnp1).hom =
          (γ.app Fm).hom ≫
            ((CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
              (op (⊤ : Opens X))).map
              ((realSingularCochainSheafComplex X).d m (m + 1)) := by
      simpa [L, Fm, Fnp1] using
        (γ.hom.naturality
          ((realSingularCochainSheafComplex X).d m (m + 1)))
    have happ := congrArg (fun f => (ConcreteCategory.hom f) β) hnat
    calc
      (ConcreteCategory.hom (γ.app Fnp1).hom) ((L.d m (m + 1)) β)
          =
        (ConcreteCategory.hom
          (L.d m (m + 1) ≫ (γ.app Fnp1).hom)) β := by
          rfl
      _ =
        (ConcreteCategory.hom
          ((γ.app Fm).hom ≫
            ((CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
              (op (⊤ : Opens X))).map
              ((realSingularCochainSheafComplex X).d m (m + 1)))) β := happ
      _ =
        ((CategoryTheory.sheafifyMap J dmn).app (op (⊤ : Opens X))) βTop := by
          rfl
  have hcycle_i :
      (L.iCycles (m + 1)) ((HomologicalComplex.cyclesMap φ (m + 1)) z) =
        (φ.f (m + 1)) ((K.iCycles (m + 1)) z) := by
    have hmorph :
        HomologicalComplex.cyclesMap φ (m + 1) ≫ L.iCycles (m + 1) =
          K.iCycles (m + 1) ≫ φ.f (m + 1) := by
      simpa [K, L, φ] using HomologicalComplex.cyclesMap_i φ (m + 1)
    exact congrArg (fun f => (ConcreteCategory.hom f) z) hmorph
  have htransport_cycle :
      (ConcreteCategory.hom (γ.app Fnp1).hom)
        ((L.iCycles (m + 1)) ((HomologicalComplex.cyclesMap φ (m + 1)) z)) =
        ((CategoryTheory.toSheafify J Pnp1).app (op (⊤ : Opens X)))
          ((K.iCycles (m + 1)) z) := by
    let t :
        ((CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
          (op (⊤ : Opens X))).obj Fnp1 :=
      ((CategoryTheory.toSheafify J Pnp1).app (op (⊤ : Opens X)))
        ((K.iCycles (m + 1)) z)
    have hcancel :
        (ConcreteCategory.hom (γ.app Fnp1).hom)
          ((ConcreteCategory.hom (γ.app Fnp1).inv) t) = t := by
      simpa using
        congrArg (fun f => (ConcreteCategory.hom f) t)
          (CategoryTheory.Iso.inv_hom_id (γ.app Fnp1))
    calc
      (ConcreteCategory.hom (γ.app Fnp1).hom)
          ((L.iCycles (m + 1)) ((HomologicalComplex.cyclesMap φ (m + 1)) z))
          =
        (ConcreteCategory.hom (γ.app Fnp1).hom)
          ((φ.f (m + 1)) ((K.iCycles (m + 1)) z)) := by
          rw [hcycle_i]
      _ = t := by
          simpa [t, φ, K, L, openSingularCochainTopToSheafifiedGlobalSections,
            J, γ, Pnp1, Fnp1, realSingularCochainSheafComplex,
            CategoryTheory.sheafSections, CategoryTheory.sheafify,
            ConcreteCategory.comp_apply] using hcancel
      _ =
        ((CategoryTheory.toSheafify J Pnp1).app (op (⊤ : Opens X)))
          ((K.iCycles (m + 1)) z) := rfl
  have hβγ :
      (ConcreteCategory.hom (γ.app Fnp1).hom) ((L.d m (m + 1)) β) =
        (ConcreteCategory.hom (γ.app Fnp1).hom)
          ((L.iCycles (m + 1)) ((HomologicalComplex.cyclesMap φ (m + 1)) z)) := by
    simpa [L, φ] using
      congrArg (fun y => (ConcreteCategory.hom (γ.app Fnp1).hom) y) hβ
  simpa [J, Pnp1, dmn, K] using
    htransport_d.symm.trans (hβγ.trans htransport_cycle)

/--
%%handwave
name:
  Local sheafified boundary representatives are local boundary representatives
statement:
  If a positive-degree top-open singular cochain cycle is locally a
  sheafified coboundary, then it is locally an ordinary singular coboundary.
proof:
  Apply local injectivity of the sheafification map to the difference between
  the local coboundary and the restricted cycle.  After shrinking the
  neighborhood this difference is zero before sheafification, and naturality
  of restriction with respect to coboundaries and cycle inclusions gives the
  required ordinary local primitive.
-/
theorem openSingularCochainTopCycleLocallyBoundary_of_locallySheafifiedBoundary
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (m : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles (m + 1))
    (hz : openSingularCochainTopCycleLocallySheafifiedBoundary X m z) :
    openSingularCochainTopCycleLocallyBoundary X m z := by
  intro x
  rcases hz x with ⟨U, hxU, β, hβ⟩
  let Pnp1 : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X (m + 1)
  let s : Pnp1.obj (op U) :=
    (((realSingularCochainOpenComplexFunctor X).obj (op U)).d m (m + 1)) β -
      (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
        ((openSingularCochainTopRestrictCycle X U (m + 1)) z)
  have hs :
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X) Pnp1).app (op U)) s = 0 := by
    simpa [Pnp1, s] using hβ
  rcases
    addCommGrp_toSheafify_eq_zero_locally
      (X := X) Pnp1 (U := U) s hs x hxU with
    ⟨V, hVU, hxV, hsV⟩
  refine ⟨V, hxV, ?_⟩
  let ρUV :=
    ((realSingularCochainOpenComplexFunctor X).map (homOfLE hVU).op)
  let βV : ((realSingularCochainOpenComplexFunctor X).obj (op V)).X m :=
    (ρUV.f m) β
  refine ⟨βV, ?_⟩
  have hsV' :
      (ρUV.f (m + 1)) s = 0 := by
    simpa [Pnp1, s, ρUV, realSingularCochainOpenPresheafComplex] using hsV
  have hsub :
      (ρUV.f (m + 1))
          ((((realSingularCochainOpenComplexFunctor X).obj (op U)).d m (m + 1)) β) -
        (ρUV.f (m + 1))
          ((((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
            ((openSingularCochainTopRestrictCycle X U (m + 1)) z)) = 0 := by
    simpa [s, map_sub] using hsV'
  have hdiff :
      (ρUV.f (m + 1))
          ((((realSingularCochainOpenComplexFunctor X).obj (op U)).d m (m + 1)) β) =
        (ρUV.f (m + 1))
          ((((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
            ((openSingularCochainTopRestrictCycle X U (m + 1)) z)) := by
    exact sub_eq_zero.mp hsub
  have hcomm :
      (ρUV.f m ≫
          ((realSingularCochainOpenComplexFunctor X).obj (op V)).d m (m + 1)) =
        ((realSingularCochainOpenComplexFunctor X).obj (op U)).d m (m + 1) ≫
          ρUV.f (m + 1) := by
    exact ρUV.comm m (m + 1)
  have hleft :
      (((realSingularCochainOpenComplexFunctor X).obj (op V)).d m (m + 1)) βV =
        (ρUV.f (m + 1))
          ((((realSingularCochainOpenComplexFunctor X).obj (op U)).d m (m + 1)) β) := by
    change
      (ConcreteCategory.hom
        (((realSingularCochainOpenComplexFunctor X).obj (op V)).d m (m + 1)))
        ((ConcreteCategory.hom (ρUV.f m)) β) =
      (ConcreteCategory.hom (ρUV.f (m + 1)))
        ((ConcreteCategory.hom
          (((realSingularCochainOpenComplexFunctor X).obj (op U)).d m (m + 1))) β)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hcomm]
  have hcycle :
      (ρUV.f (m + 1))
          ((((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
            ((openSingularCochainTopRestrictCycle X U (m + 1)) z)) =
        (((realSingularCochainOpenComplexFunctor X).obj (op V)).iCycles (m + 1))
          ((openSingularCochainTopRestrictCycle X V (m + 1)) z) := by
    have hUtop : U ≤ (⊤ : Opens X) := by
      intro y _hy
      trivial
    have hVtop : V ≤ (⊤ : Opens X) := by
      intro y _hy
      trivial
    let ρTopU :=
      ((realSingularCochainOpenComplexFunctor X).map (homOfLE hUtop).op)
    let ρTopV :=
      ((realSingularCochainOpenComplexFunctor X).map (homOfLE hVtop).op)
    have hρcomp : ρTopU ≫ ρUV = ρTopV := by
      have hmap :=
        ((realSingularCochainOpenComplexFunctor X).map_comp
          (homOfLE hUtop).op (homOfLE hVU).op).symm
      simpa [ρTopU, ρTopV, ρUV,
        Subsingleton.elim ((homOfLE hUtop).op ≫ (homOfLE hVU).op)
          (homOfLE hVtop).op] using hmap
    have hcycles :
        (HomologicalComplex.cyclesMap ρUV (m + 1))
            ((openSingularCochainTopRestrictCycle X U (m + 1)) z) =
          (openSingularCochainTopRestrictCycle X V (m + 1)) z := by
      calc
        (HomologicalComplex.cyclesMap ρUV (m + 1))
            ((openSingularCochainTopRestrictCycle X U (m + 1)) z)
            =
          (HomologicalComplex.cyclesMap ρUV (m + 1))
            ((HomologicalComplex.cyclesMap ρTopU (m + 1)) z) := by
            simp [openSingularCochainTopRestrictCycle, ρTopU]
        _ =
          (HomologicalComplex.cyclesMap (ρTopU ≫ ρUV) (m + 1)) z := by
            have hmap :=
              congrArg (fun f => (ConcreteCategory.hom f) z)
                (HomologicalComplex.cyclesMap_comp ρTopU ρUV (m + 1))
            simpa [ConcreteCategory.comp_apply] using hmap.symm
        _ =
          (HomologicalComplex.cyclesMap ρTopV (m + 1)) z := by
            rw [hρcomp]
        _ =
          (openSingularCochainTopRestrictCycle X V (m + 1)) z := by
            simp [openSingularCochainTopRestrictCycle, ρTopV]
    have hcycle_i :
        (ρUV.f (m + 1))
            ((((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
              ((openSingularCochainTopRestrictCycle X U (m + 1)) z)) =
          (((realSingularCochainOpenComplexFunctor X).obj (op V)).iCycles (m + 1))
            ((HomologicalComplex.cyclesMap ρUV (m + 1))
              ((openSingularCochainTopRestrictCycle X U (m + 1)) z)) := by
      have hmorph :
          HomologicalComplex.cyclesMap ρUV (m + 1) ≫
              ((realSingularCochainOpenComplexFunctor X).obj (op V)).iCycles (m + 1) =
            ((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1) ≫
              ρUV.f (m + 1) := by
        simpa [ρUV] using HomologicalComplex.cyclesMap_i ρUV (m + 1)
      have happ :=
        congrArg
          (fun f => (ConcreteCategory.hom f)
            ((openSingularCochainTopRestrictCycle X U (m + 1)) z))
          hmorph
      simpa [ConcreteCategory.comp_apply] using happ.symm
    calc
      (ρUV.f (m + 1))
          ((((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
            ((openSingularCochainTopRestrictCycle X U (m + 1)) z))
          =
        (((realSingularCochainOpenComplexFunctor X).obj (op V)).iCycles (m + 1))
          ((HomologicalComplex.cyclesMap ρUV (m + 1))
            ((openSingularCochainTopRestrictCycle X U (m + 1)) z)) := hcycle_i
      _ =
        (((realSingularCochainOpenComplexFunctor X).obj (op V)).iCycles (m + 1))
          ((openSingularCochainTopRestrictCycle X V (m + 1)) z) := by
          rw [hcycles]
  calc
    (((realSingularCochainOpenComplexFunctor X).obj (op V)).d m (m + 1)) βV
        =
      (ρUV.f (m + 1))
        ((((realSingularCochainOpenComplexFunctor X).obj (op U)).d m (m + 1)) β) := hleft
    _ =
      (ρUV.f (m + 1))
        ((((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles (m + 1))
          ((openSingularCochainTopRestrictCycle X U (m + 1)) z)) := hdiff
    _ =
      (((realSingularCochainOpenComplexFunctor X).obj (op V)).iCycles (m + 1))
        ((openSingularCochainTopRestrictCycle X V (m + 1)) z) := hcycle

/--
%%handwave
name:
  A global sheafified primitive gives local sheafified boundary representatives
statement:
  If the sheafified image of a top-open singular \((m+1)\)-cochain cycle is
  the coboundary of a global sheafified \(m\)-cochain, then the original
  cycle is locally a sheafified ordinary coboundary.
proof:
  Represent the global sheafified primitive locally by ordinary singular
  \(m\)-cochains.  Naturality of the sheafification map with respect to the
  coboundary, together with the global sheafified primitive identity, gives
  the required local equality after sheafification.
-/
theorem openSingularCochainTopCycleLocallySheafifiedBoundary_succ_of_sheafified_globalPrimitive
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (m : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles (m + 1))
    (β :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).X m))
    (hβ :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).d m (m + 1)) β =
        ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).iCycles (m + 1))
          ((HomologicalComplex.cyclesMap
            (openSingularCochainTopToSheafifiedGlobalSections X) (m + 1)) z)) :
    openSingularCochainTopCycleLocallySheafifiedBoundary X m z := by
  rcases
    openSingularCochainTop_exists_topOpenSheafifiedPrimitive_of_globalSectionsPrimitive
      (X := X) m z β hβ with
    ⟨βTop, hβTop⟩
  exact
    openSingularCochainTopCycleLocallySheafifiedBoundary_of_topOpenPrimitive
      (X := X) m z βTop hβTop

/--
%%handwave
name:
  A global sheafified primitive gives local boundary representatives
statement:
  If the sheafified image of a top-open singular \((m+1)\)-cochain cycle is
  the coboundary of a global sheafified \(m\)-cochain, then the original
  cycle is locally an ordinary singular coboundary.
proof:
  Represent the global sheafified primitive locally by ordinary singular
  \(m\)-cochains.  Restrict the sheafified coboundary identity to such a
  neighborhood, compare it with the sheafification of the ordinary
  coboundary, and use local injectivity of the sheafification unit after
  shrinking once more.
-/
theorem openSingularCochainTopCycleLocallyBoundary_succ_of_sheafified_globalPrimitive
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (m : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles (m + 1))
    (β :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).X m))
    (hβ :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).d m (m + 1)) β =
        ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).iCycles (m + 1))
          ((HomologicalComplex.cyclesMap
            (openSingularCochainTopToSheafifiedGlobalSections X) (m + 1)) z)) :
    openSingularCochainTopCycleLocallyBoundary X m z := by
  exact
    openSingularCochainTopCycleLocallyBoundary_of_locallySheafifiedBoundary
      (X := X) m z
      (openSingularCochainTopCycleLocallySheafifiedBoundary_succ_of_sheafified_globalPrimitive
        (X := X) m z β hβ)

/--
%%handwave
name:
  A global sheafified primitive gives locally zero top-open singular class
statement:
  If the sheafified image of a top-open singular \((m+1)\)-cochain cycle is
  the coboundary of a global sheafified \(m\)-cochain, then the original
  cycle has locally zero ordinary singular cohomology class.
proof:
  Represent the global sheafified primitive locally by ordinary singular
  \(m\)-cochains.  The sheafified coboundary identity and local injectivity
  of the sheafification unit imply, after shrinking, that the restricted
  original cycle is the ordinary coboundary of the local representative.
-/
theorem openSingularCochainTopCycleLocallyZero_succ_of_sheafified_globalPrimitive
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (m : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles (m + 1))
    (β :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).X m))
    (hβ :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).d m (m + 1)) β =
        ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).iCycles (m + 1))
          ((HomologicalComplex.cyclesMap
            (openSingularCochainTopToSheafifiedGlobalSections X) (m + 1)) z)) :
    openSingularCochainTopCycleLocallyZero X (m + 1) z := by
  intro x
  rcases
    openSingularCochainTopCycleLocallyBoundary_succ_of_sheafified_globalPrimitive
      (X := X) m z β hβ x with
    ⟨U, hxU, βU, hβU⟩
  refine ⟨U, hxU, ?_⟩
  exact
    cochainComplex_addCommGrp_homologyπ_eq_zero_of_preimage
      (K := (realSingularCochainOpenComplexFunctor X).obj (op U))
      m ((openSingularCochainTopRestrictCycle X U (m + 1)) z) βU hβU

/--
%%handwave
name:
  A zero degree-zero sheafified top-open class is zero as a sheafified cycle
statement:
  If the image of a top-open singular zero-cochain cycle has zero
  cohomology class in the global sections of the sheafified cochain complex,
  then the sheafified global zero-cycle itself is zero.
proof:
  Apply [a zero degree-zero cohomology class in an abelian cochain complex is zero as a cycle](lean:JJMath.Cohomology.cochainComplex_addCommGrp_cycle_zero_of_homologyπ_zero_eq_zero) to the global-sections cochain complex.
-/
theorem openSingularCochainTopToSheafifiedGlobalSections_cycle_zero_of_homologyπ_zero_eq_zero
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles 0)
    (hz :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).homologyπ 0)
        ((HomologicalComplex.cyclesMap
          (openSingularCochainTopToSheafifiedGlobalSections X) 0) z) = 0) :
    (HomologicalComplex.cyclesMap
      (openSingularCochainTopToSheafifiedGlobalSections X) 0) z = 0 := by
  let L :=
    (((Sheaf.Γ (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
      (realSingularCochainSheafComplex X))
  exact
    cochainComplex_addCommGrp_cycle_zero_of_homologyπ_zero_eq_zero
      (K := L)
      ((HomologicalComplex.cyclesMap
        (openSingularCochainTopToSheafifiedGlobalSections X) 0) z)
      hz

/--
%%handwave
name:
  A top-open zero-cochain whose sheafification vanishes is locally zero as a cycle
statement:
  If the sheafification of the underlying top-open singular zero-cochain is
  zero, then the corresponding top-open zero-cycle restricts to zero on a
  neighborhood of every point.
proof:
  A section that sheafifies to zero is locally zero before sheafification.
  Apply this to the degree-zero singular-cochain presheaf, and use
  naturality of the cycle inclusion to identify restriction of the
  underlying cochain with the underlying cochain of the restricted cycle.
-/
theorem openSingularCochainTopCycleLocallyZeroAsCycle_of_toSheafify_iCycles_eq_zero
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles 0)
    (hz :
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).X 0)).app
          (op (⊤ : Opens X)))
        ((((realSingularCochainOpenComplexFunctor X).obj
          (op (⊤ : Opens X))).iCycles 0) z) = 0) :
    openSingularCochainTopCycleLocallyZeroAsCycle X z := by
  intro x
  rcases
    addCommGrp_toSheafify_eq_zero_locally
      (X := X) ((realSingularCochainOpenPresheafComplex X).X 0)
      (U := (⊤ : Opens X))
      ((((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).iCycles 0) z)
      hz x (by trivial) with
    ⟨U, hUtop, hxU, hres⟩
  refine ⟨U, hxU, ?_⟩
  apply
    (AddCommGrpCat.mono_iff_injective
      (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles 0)).1
      inferInstance
  have hcycle_i :
      (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles 0)
          ((openSingularCochainTopRestrictCycle X U 0) z) =
        (((realSingularCochainOpenComplexFunctor X).map
          (homOfLE hUtop).op).f 0)
          ((((realSingularCochainOpenComplexFunctor X).obj
            (op (⊤ : Opens X))).iCycles 0) z) := by
    change
      (ConcreteCategory.hom
        (openSingularCochainTopRestrictCycle X U 0 ≫
          ((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles 0)) z =
      (ConcreteCategory.hom
        (((realSingularCochainOpenComplexFunctor X).obj
            (op (⊤ : Opens X))).iCycles 0 ≫
          ((realSingularCochainOpenComplexFunctor X).map
            (homOfLE hUtop).op).f 0)) z
    have hmorph :
        openSingularCochainTopRestrictCycle X U 0 ≫
            ((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles 0 =
          ((realSingularCochainOpenComplexFunctor X).obj
              (op (⊤ : Opens X))).iCycles 0 ≫
            ((realSingularCochainOpenComplexFunctor X).map
              (homOfLE hUtop).op).f 0 := by
      simpa [openSingularCochainTopRestrictCycle] using
        (HomologicalComplex.cyclesMap_i
          (((realSingularCochainOpenComplexFunctor X).map
            (homOfLE hUtop).op)) 0)
    exact congrArg (fun f => (ConcreteCategory.hom f) z) hmorph
  have hres' :
      (((realSingularCochainOpenComplexFunctor X).map
          (homOfLE hUtop).op).f 0)
          ((((realSingularCochainOpenComplexFunctor X).obj
            (op (⊤ : Opens X))).iCycles 0) z) = 0 := by
    simpa [realSingularCochainOpenPresheafComplex] using hres
  calc
    (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles 0)
        ((openSingularCochainTopRestrictCycle X U 0) z)
        =
      (((realSingularCochainOpenComplexFunctor X).map
        (homOfLE hUtop).op).f 0)
        ((((realSingularCochainOpenComplexFunctor X).obj
          (op (⊤ : Opens X))).iCycles 0) z) := hcycle_i
    _ = 0 := hres'
    _ =
      (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles 0)
        (0 : ((realSingularCochainOpenComplexFunctor X).obj (op U)).cycles 0) := by
        exact
          (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles 0).hom.map_zero.symm

/--
%%handwave
name:
  A zero sheafified degree-zero cycle has zero sheafification-unit image
statement:
  If the image of a top-open singular zero-cycle is zero as a global
  sheafified cycle, then the sheafification-unit image of its underlying
  top-open zero-cochain is zero.
proof:
  Apply naturality of the cycle inclusion to the cochain map from top-open
  singular cochains to global sheafified cochains.  The degree-zero component
  of this cochain map is the sheafification unit followed by the standard
  identification of global sections with sections over the top open.  Cancel
  this identification isomorphism.
-/
theorem openSingularCochainTopToSheafifiedGlobalSections_toSheafify_iCycles_eq_zero_of_cycle_eq_zero
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles 0)
    (hz :
      (HomologicalComplex.cyclesMap
        (openSingularCochainTopToSheafifiedGlobalSections X) 0) z = 0) :
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).X 0)).app
          (op (⊤ : Opens X)))
        ((((realSingularCochainOpenComplexFunctor X).obj
          (op (⊤ : Opens X))).iCycles 0) z) = 0 := by
  let J := Opens.grothendieckTopology X
  let K := (realSingularCochainOpenComplexFunctor X).obj (op (⊤ : Opens X))
  let L :=
    (((Sheaf.Γ J AddCommGrpCat.{v}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
      (realSingularCochainSheafComplex X))
  let φ := openSingularCochainTopToSheafifiedGlobalSections X
  have hφi : (φ.f 0) ((K.iCycles 0) z) = 0 := by
    have hcycle_i :
        (L.iCycles 0) ((HomologicalComplex.cyclesMap φ 0) z) =
          (φ.f 0) ((K.iCycles 0) z) := by
      have hmorph :
          HomologicalComplex.cyclesMap φ 0 ≫ L.iCycles 0 =
            K.iCycles 0 ≫ φ.f 0 := by
        simpa [K, L, φ] using HomologicalComplex.cyclesMap_i φ 0
      exact congrArg (fun f => (ConcreteCategory.hom f) z) hmorph
    have hleft :
        (L.iCycles 0) ((HomologicalComplex.cyclesMap φ 0) z) = 0 := by
      rw [hz]
      exact (L.iCycles 0).hom.map_zero
    exact hcycle_i.symm.trans hleft
  letI : OrderTop (Opens X) :=
    { top := (⊤ : Opens X)
      le_top := fun _ => by
        intro _ _
        trivial }
  have hTop : IsTerminal (⊤ : Opens X) := by
    exact CategoryTheory.Limits.isTerminalTop
  let γ : Sheaf.Γ J AddCommGrpCat.{v} ≅
      (CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
        (op (⊤ : Opens X)) :=
    CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (J := J) (A := AddCommGrpCat.{v})
      (T := (⊤ : Opens X)) hTop
  let F0 := (realSingularCochainSheafComplex X).X 0
  let t : ((CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
        (op (⊤ : Opens X))).obj F0 :=
    (((CategoryTheory.toSheafify J
      ((realSingularCochainOpenPresheafComplex X).X 0)).app
        (op (⊤ : Opens X)))
      ((K.iCycles 0) z))
  have hcomp :
      (ConcreteCategory.hom
        (γ.app F0).inv) t = 0 := by
    simpa [φ, K, L, openSingularCochainTopToSheafifiedGlobalSections, J, γ] using hφi
  have hcancel :=
    congrArg
      (fun y =>
        (ConcreteCategory.hom
          (γ.app F0).hom) y)
      hcomp
  have hleft :
      (ConcreteCategory.hom (γ.app F0).hom)
        ((ConcreteCategory.hom (γ.app F0).inv) t) = t := by
    simpa using
      congrArg (fun f => (ConcreteCategory.hom f) t)
        (CategoryTheory.Iso.inv_hom_id (γ.app F0))
  have hright :
      (ConcreteCategory.hom (γ.app F0).hom) 0 = 0 :=
    (γ.app F0).hom.hom.map_zero
  change t = 0
  calc
    t = (ConcreteCategory.hom (γ.app F0).hom)
        ((ConcreteCategory.hom (γ.app F0).inv) t) := hleft.symm
    _ = (ConcreteCategory.hom (γ.app F0).hom) 0 := hcancel
    _ = 0 := hright

/--
%%handwave
name:
  A zero sheafified degree-zero cycle has locally zero singular class
statement:
  If the sheafified image of a top-open singular zero-cochain cycle is zero
  as a global sheafified cycle, then the original cycle has locally zero
  ordinary degree-zero singular cohomology class.
proof:
  Use local injectivity of the sheafification unit: after shrinking around
  each point, the original singular zero-cochain restricts to zero, hence its
  local degree-zero cohomology class is zero.
-/
theorem openSingularCochainTopCycleLocallyZero_zero_of_sheafified_cycle_eq_zero
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles 0)
    (hz :
      (HomologicalComplex.cyclesMap
        (openSingularCochainTopToSheafifiedGlobalSections X) 0) z = 0) :
    openSingularCochainTopCycleLocallyZero X 0 z := by
  exact
    openSingularCochainTopCycleLocallyZero_of_cycleLocallyZeroAsCycle
      (X := X) z
      (openSingularCochainTopCycleLocallyZeroAsCycle_of_toSheafify_iCycles_eq_zero
        (X := X) z
        (openSingularCochainTopToSheafifiedGlobalSections_toSheafify_iCycles_eq_zero_of_cycle_eq_zero
          (X := X) z hz))

/--
%%handwave
name:
  Zero sheafified degree-zero class implies locally zero singular class
statement:
  If a top-open singular zero-cochain cycle has zero cohomology class after
  passing to global sections of the sheafified singular-cochain complex, then
  its ordinary degree-zero singular cohomology class is locally zero.
proof:
  In degree zero, a zero cohomology class means the corresponding sheafified
  closed zero-cochain is locally the zero section.  Since the sheafification
  unit is locally injective and locally represented by ordinary singular
  cochains, after shrinking the original zero-cochain has zero local
  cohomology class.
-/
theorem openSingularCochainTopToSheafifiedGlobalSections_cycle_locallyZero_zero_of_sheafified
    (X : TopCat.{v})
    [ParacompactSpace X]
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles 0)
    (hz :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).homologyπ 0)
        ((HomologicalComplex.cyclesMap
          (openSingularCochainTopToSheafifiedGlobalSections X) 0) z) = 0) :
    openSingularCochainTopCycleLocallyZero X 0 z := by
  exact
    openSingularCochainTopCycleLocallyZero_zero_of_sheafified_cycle_eq_zero
      (X := X) z
      (openSingularCochainTopToSheafifiedGlobalSections_cycle_zero_of_homologyπ_zero_eq_zero
        (X := X) z hz)

/--
%%handwave
name:
  Zero sheafified positive-degree class implies locally zero singular class
statement:
  If a top-open singular \((m+1)\)-cochain cycle has zero cohomology class
  after passing to global sections of the sheafified singular-cochain
  complex, then its ordinary singular cohomology class is locally zero.
proof:
  A zero sheafified cohomology class is locally a coboundary.  The
  sheafification unit is locally represented by ordinary singular cochains,
  so after shrinking, the original cycle has a local singular primitive.
-/
theorem openSingularCochainTopToSheafifiedGlobalSections_cycle_locallyZero_succ_of_sheafified
    (X : TopCat.{v})
    [ParacompactSpace X] (_hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (m : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles (m + 1))
    (hz :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).homologyπ (m + 1))
        ((HomologicalComplex.cyclesMap
          (openSingularCochainTopToSheafifiedGlobalSections X) (m + 1)) z) = 0) :
    openSingularCochainTopCycleLocallyZero X (m + 1) z := by
  rcases
    openSingularCochainTopToSheafifiedGlobalSections_exists_primitive_succ_of_homologyπ_eq_zero
      (X := X) m z hz with
    ⟨β, hβ⟩
  exact
    openSingularCochainTopCycleLocallyZero_succ_of_sheafified_globalPrimitive
      (X := X) m z β hβ

/--
%%handwave
name:
  Zero sheafified class implies locally zero singular class
statement:
  If a top-open singular cochain cycle has zero cohomology class after
  passing to global sections of the sheafified singular-cochain complex, then
  its ordinary singular cohomology class is locally zero.
proof:
  Split by degree.  Degree zero is local vanishing of a sheafified
  zero-cochain; positive degree is local existence of singular primitives.
-/
theorem openSingularCochainTopToSheafifiedGlobalSections_cycle_locallyZero_of_sheafified
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (n : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles n)
    (hz :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).homologyπ n)
        ((HomologicalComplex.cyclesMap
          (openSingularCochainTopToSheafifiedGlobalSections X) n) z) = 0) :
    openSingularCochainTopCycleLocallyZero X n z := by
  cases n with
  | zero =>
      exact
        openSingularCochainTopToSheafifiedGlobalSections_cycle_locallyZero_zero_of_sheafified
          (X := X) z hz
  | succ m =>
      exact
        openSingularCochainTopToSheafifiedGlobalSections_cycle_locallyZero_succ_of_sheafified
          (X := X) hloc m z hz

/--
%%handwave
name:
  Top-open singular zero-cochains are locally determined
statement:
  If a singular zero-cochain on the whole space restricts to zero on a
  neighborhood of every point, then it is zero.
proof:
  Singular zero-cochains are functions on singular vertices, hence on points.
  Evaluating at any point and restricting to a neighborhood on which the
  cochain vanishes shows that the value at that point is zero.
-/
theorem openSingularCochainTop_zeroCochain_eq_zero_of_locallyZero
    (X : TopCat.{v})
    (α :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).X 0)
    (hα :
      ∀ x : X, ∃ U : Opens X, x ∈ U ∧
        (((realSingularCochainOpenComplexFunctor X).map
          (homOfLE (show U ≤ (⊤ : Opens X) from by
            intro y _hy
            trivial)).op).f 0) α = 0) :
    α = 0 := by
  let T : TopCat.{v} := (Opens.toTopCat X).obj (⊤ : Opens X)
  have hα' : (α : (SingularCochainComplex ℝ T).X 0) = 0 := by
    apply singularZeroCochain_eq_zero_of_forall_vertex_eval_zero
    intro t
    let y : T := TopCat.toSSetObj₀Equiv t
    let yTop : (⊤ : Opens X) := by
      simpa [T] using y
    let x : X := yTop
    rcases hα x with ⟨U, hyU, hUzero⟩
    have hUtop : U ≤ (⊤ : Opens X) := by
      intro x _hx
      trivial
    let i : U ⟶ (⊤ : Opens X) := homOfLE hUtop
    let f : (Opens.toTopCat X).obj U ⟶ T := (Opens.toTopCat X).map i
    let yU : (Opens.toTopCat X).obj U := ⟨x, hyU⟩
    let tU : (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).obj
        (op (SimplexCategory.mk 0)) :=
      TopCat.toSSetObj₀Equiv.symm yU
    have h_eval_restrict :
        Sigma.ι
            (fun _ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).obj
                (op (SimplexCategory.mk 0)) =>
              SingularCohomologyCoefficient.{0, v} ℝ) tU ≫
            (singularChainsDegreeZeroCoproductIso
              ((Opens.toTopCat X).obj U)).inv ≫
            (((realSingularCochainOpenComplexFunctor X).map i.op).f 0) α = 0 := by
      have hcongr :=
        congrArg
          (fun β =>
            Sigma.ι
                (fun _ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).obj
                    (op (SimplexCategory.mk 0)) =>
                  SingularCohomologyCoefficient.{0, v} ℝ) tU ≫
                (singularChainsDegreeZeroCoproductIso
                  ((Opens.toTopCat X).obj U)).inv ≫ β)
          hUzero
      simpa [i] using hcongr
    have hpull :
        Sigma.ι
            (fun _ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).obj
                (op (SimplexCategory.mk 0)) =>
              SingularCohomologyCoefficient.{0, v} ℝ) tU ≫
            (singularChainsDegreeZeroCoproductIso
              ((Opens.toTopCat X).obj U)).inv ≫
            (((realSingularCochainOpenComplexFunctor X).map i.op).f 0) α =
          Sigma.ι
            (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
              SingularCohomologyCoefficient.{0, v} ℝ)
            (((TopCat.toSSet.map f).app (op (SimplexCategory.mk 0))) tU) ≫
            (singularChainsDegreeZeroCoproductIso T).inv ≫
            (α : (SingularCochainComplex ℝ T).X 0) := by
      simpa [T, f, i, realSingularCochainOpenComplexFunctor,
        realSingularCochainOpenModuleComplexFunctor, realSingularCochainComplexAddFunctor]
        using
          singularZeroCochain_eval_pullback
            (f := f) (α := (α : (SingularCochainComplex ℝ T).X 0)) tU
    have himage :
        ((TopCat.toSSet.map f).app (op (SimplexCategory.mk 0))) tU = t := by
      apply TopCat.toSSetObj₀Equiv.injective
      change f yU = y
      change (f yU : (⊤ : Opens X)) = yTop
      apply Subtype.ext
      simp [yU, yTop, x, f, i, T]
    have h_eval_original :
        Sigma.ι
            (fun _ : (TopCat.toSSet.obj T).obj (op (SimplexCategory.mk 0)) =>
              SingularCohomologyCoefficient.{0, v} ℝ)
            (((TopCat.toSSet.map f).app (op (SimplexCategory.mk 0))) tU) ≫
            (singularChainsDegreeZeroCoproductIso T).inv ≫
            (α : (SingularCochainComplex ℝ T).X 0) = 0 :=
      hpull.symm.trans h_eval_restrict
    simpa [himage]
      using h_eval_original
  simpa [T, realSingularCochainOpenComplexFunctor,
    realSingularCochainOpenModuleComplexFunctor, realSingularCochainComplexAddFunctor]
    using hα'

/--
%%handwave
name:
  Locally zero restricted degree-zero cycles are globally zero
statement:
  If a singular zero-cochain cycle on the whole space restricts to the zero
  cycle on a neighborhood of every point, then the original zero-cycle is
  zero.
proof:
  A singular zero-cochain is an arbitrary function on singular vertices,
  equivalently on points.  For each vertex, choose a neighborhood on which the
  restricted cycle is zero.  Evaluating the restriction at that vertex shows
  that the original zero-cochain has value zero there.
-/
theorem openSingularCochainTopCycle_eq_zero_of_locallyZeroAsCycle
    (X : TopCat.{v})
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles 0)
    (hz : openSingularCochainTopCycleLocallyZeroAsCycle X z) :
    z = 0 := by
  let K := (realSingularCochainOpenComplexFunctor X).obj (op (⊤ : Opens X))
  apply (AddCommGrpCat.mono_iff_injective (K.iCycles 0)).1 inferInstance
  have hα :
      ∀ x : X, ∃ U : Opens X, x ∈ U ∧
        (((realSingularCochainOpenComplexFunctor X).map
          (homOfLE (show U ≤ (⊤ : Opens X) from by
            intro y _hy
            trivial)).op).f 0) ((K.iCycles 0) z) = 0 := by
    intro x
    rcases hz x with ⟨U, hxU, hzU⟩
    have hUtop : U ≤ (⊤ : Opens X) := by
      intro y _hy
      trivial
    let ρTopU :=
      ((realSingularCochainOpenComplexFunctor X).map (homOfLE hUtop).op)
    refine ⟨U, hxU, ?_⟩
    have hcycle_i :
        (ρTopU.f 0) ((K.iCycles 0) z) =
          (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles 0)
            ((openSingularCochainTopRestrictCycle X U 0) z) := by
      have hmorph :
          openSingularCochainTopRestrictCycle X U 0 ≫
              ((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles 0 =
            K.iCycles 0 ≫ ρTopU.f 0 := by
        simpa [K, openSingularCochainTopRestrictCycle, ρTopU] using
          (HomologicalComplex.cyclesMap_i ρTopU 0)
      have happ := congrArg (fun f => (ConcreteCategory.hom f) z) hmorph
      simpa [ConcreteCategory.comp_apply] using happ.symm
    calc
      (((realSingularCochainOpenComplexFunctor X).map
          (homOfLE (show U ≤ (⊤ : Opens X) from by
            intro y _hy
            trivial)).op).f 0) ((K.iCycles 0) z)
          =
        (ρTopU.f 0) ((K.iCycles 0) z) := by
          simp [ρTopU]
      _ =
        (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles 0)
          ((openSingularCochainTopRestrictCycle X U 0) z) := hcycle_i
      _ = 0 := by
          rw [hzU]
          exact
            (((realSingularCochainOpenComplexFunctor X).obj (op U)).iCycles 0).hom.map_zero
  have hzero :
      (K.iCycles 0) z = 0 :=
    openSingularCochainTop_zeroCochain_eq_zero_of_locallyZero
      (X := X) ((K.iCycles 0) z) hα
  calc
    (K.iCycles 0) z = 0 := hzero
    _ = (K.iCycles 0) 0 := (K.iCycles 0).hom.map_zero.symm

/--
%%handwave
name:
  Locally zero degree-zero restricted cycles have zero global class
statement:
  If a singular zero-cochain cycle on the whole space vanishes as a
  restricted zero-cycle on a neighborhood of every point, then its global
  degree-zero singular cohomology class is zero.
proof:
  A singular zero-cochain is determined by its values on singular vertices,
  namely points of the space.  Local vanishing around every point makes all
  these values zero, so the global zero-cycle and hence its degree-zero
  cohomology class are zero.
-/
theorem openSingularCochainTop_homologyπ_zero_eq_zero_of_cycle_locallyZeroAsCycle
    (X : TopCat.{v})
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles 0)
    (hz : openSingularCochainTopCycleLocallyZeroAsCycle X z) :
    (((realSingularCochainOpenComplexFunctor X).obj
      (op (⊤ : Opens X))).homologyπ 0) z = 0 := by
  rw [openSingularCochainTopCycle_eq_zero_of_locallyZeroAsCycle (X := X) z hz]
  exact
    (((realSingularCochainOpenComplexFunctor X).obj
      (op (⊤ : Opens X))).homologyπ 0).hom.map_zero

/--
%%handwave
name:
  Locally zero degree-zero top-open cycles have zero global class
statement:
  If a singular zero-cochain cycle on the whole space has locally zero
  degree-zero singular cohomology class, then its global degree-zero singular
  cohomology class is zero.
proof:
  A degree-zero singular cocycle is locally constant on path components.
  Local vanishing forces these local constants to be zero, and the sheaf
  condition for locally constant functions glues this to global vanishing.
-/
theorem openSingularCochainTop_homologyπ_zero_eq_zero_of_cycle_locallyZero
    (X : TopCat.{v})
    [ParacompactSpace X]
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles 0)
    (hz : openSingularCochainTopCycleLocallyZero X 0 z) :
    (((realSingularCochainOpenComplexFunctor X).obj
      (op (⊤ : Opens X))).homologyπ 0) z = 0 := by
  exact
    openSingularCochainTop_homologyπ_zero_eq_zero_of_cycle_locallyZeroAsCycle
      (X := X) z
      (openSingularCochainTopCycleLocallyZeroAsCycle_of_cycleLocallyZero
        (X := X) z hz)

/--
%%handwave
name:
  Sheafified-boundary subdivision kills a degree-zero top-open cycle class
statement:
  If a singular zero-cochain cycle on the whole space has zero class in the
  global sections of the sheafified singular-cochain complex, then its
  ordinary degree-zero singular cohomology class is zero.
proof:
  In degree zero, the vanishing sheafified class says the associated
  locally constant zero-cochain is locally zero.  The sheaf condition and
  local injectivity of sheafification identify the original global
  zero-cochain class with zero.
-/
theorem openSingularCochainTop_homologyπ_zero_eq_zero_of_sheafified_boundary_subdivision
    (X : TopCat.{v})
    [ParacompactSpace X]
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles 0)
    (hz :
      ((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (realSingularCochainSheafComplex X)).homologyπ 0)
        ((HomologicalComplex.cyclesMap
          (openSingularCochainTopToSheafifiedGlobalSections X) 0) z) = 0) :
    (((realSingularCochainOpenComplexFunctor X).obj
      (op (⊤ : Opens X))).homologyπ 0) z = 0 := by
  exact
    openSingularCochainTop_homologyπ_zero_eq_zero_of_cycle_locallyZero
      (X := X) z
      (openSingularCochainTopToSheafifiedGlobalSections_cycle_locallyZero_zero_of_sheafified
        (X := X) z hz)

/--
%%handwave
name:
  Representatives of one sheafified singular cochain agree locally on overlaps
statement:
  If two ordinary singular cochains on two members of an open cover represent
  the same sheafified section after restriction, then near every point of the
  overlap their further restrictions agree as ordinary cochains.
proof:
  Restrict both representatives to the intersection.  Their images in the
  sheafification agree by naturality and because both represent the same
  ambient sheafified section.  Local injectivity of the sheafification map
  then gives a smaller neighborhood on which the ordinary restrictions are
  equal.
-/
theorem realSingularCochainOpenPresheafComplex_openCover_localCompatibility_of_represent_same_sheafified_section
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (p : ℕ) (U : Opens X)
    {ι : Type v}
    (V : ι → Opens X)
    (hVU : ∀ i : ι, V i ≤ U)
    (s :
      (CategoryTheory.sheafify
        (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).X p)).obj (op U))
    (t : ∀ i : ι,
      ((realSingularCochainOpenPresheafComplex X).X p).obj (op (V i)))
    (ht : ∀ i : ι,
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).X p)).app
          (op (V i))) (t i) =
        (CategoryTheory.sheafify
          (Opens.grothendieckTopology X)
          ((realSingularCochainOpenPresheafComplex X).X p)).map
            (homOfLE (hVU i)).op s) :
    ∀ (i j : ι) (x : X), x ∈ V i → x ∈ V j →
      ∃ (W : Opens X) (hWi : W ≤ V i) (hWj : W ≤ V j), x ∈ W ∧
        ((realSingularCochainOpenPresheafComplex X).X p).map
            (homOfLE hWi).op (t i) =
          ((realSingularCochainOpenPresheafComplex X).X p).map
            (homOfLE hWj).op (t j) := by
  intro i j x hxi hxj
  let J := Opens.grothendieckTopology X
  let P : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X p
  let W₀ : Opens X := V i ⊓ V j
  have hW₀i : W₀ ≤ V i := by
    exact inf_le_left
  have hW₀j : W₀ ≤ V j := by
    exact inf_le_right
  let a : P.obj (op W₀) := P.map (homOfLE hW₀i).op (t i)
  let b : P.obj (op W₀) := P.map (homOfLE hW₀j).op (t j)
  have hxW₀ : x ∈ W₀ := ⟨hxi, hxj⟩
  have hηa :
      ((CategoryTheory.toSheafify J P).app (op W₀)) a =
        ((CategoryTheory.sheafify J P).map
          (homOfLE (show W₀ ≤ U from le_trans hW₀i (hVU i))).op) s := by
    have hnat :=
      (CategoryTheory.toSheafify J P).naturality (homOfLE hW₀i).op
    have happ := congrArg (fun f => (ConcreteCategory.hom f) (t i)) hnat
    calc
      ((CategoryTheory.toSheafify J P).app (op W₀)) a =
        ((CategoryTheory.sheafify J P).map (homOfLE hW₀i).op)
          (((CategoryTheory.toSheafify J P).app (op (V i))) (t i)) := by
          simpa [J, P, a, ConcreteCategory.comp_apply] using happ.symm
      _ =
        ((CategoryTheory.sheafify J P).map (homOfLE hW₀i).op)
          (((CategoryTheory.sheafify J P).map (homOfLE (hVU i)).op) s) := by
          rw [ht i]
      _ =
        ((CategoryTheory.sheafify J P).map
          (homOfLE (show W₀ ≤ U from le_trans hW₀i (hVU i))).op) s := by
          have hmap :=
            (CategoryTheory.sheafify J P).map_comp
              (homOfLE (hVU i)).op (homOfLE hW₀i).op
          have hcomp :
              (homOfLE (hVU i)).op ≫ (homOfLE hW₀i).op =
                (homOfLE (show W₀ ≤ U from le_trans hW₀i (hVU i))).op := by
            exact Subsingleton.elim _ _
          rw [← ConcreteCategory.comp_apply, ← hmap, hcomp]
  have hηb :
      ((CategoryTheory.toSheafify J P).app (op W₀)) b =
        ((CategoryTheory.sheafify J P).map
          (homOfLE (show W₀ ≤ U from le_trans hW₀j (hVU j))).op) s := by
    have hnat :=
      (CategoryTheory.toSheafify J P).naturality (homOfLE hW₀j).op
    have happ := congrArg (fun f => (ConcreteCategory.hom f) (t j)) hnat
    calc
      ((CategoryTheory.toSheafify J P).app (op W₀)) b =
        ((CategoryTheory.sheafify J P).map (homOfLE hW₀j).op)
          (((CategoryTheory.toSheafify J P).app (op (V j))) (t j)) := by
          simpa [J, P, b, ConcreteCategory.comp_apply] using happ.symm
      _ =
        ((CategoryTheory.sheafify J P).map (homOfLE hW₀j).op)
          (((CategoryTheory.sheafify J P).map (homOfLE (hVU j)).op) s) := by
          rw [ht j]
      _ =
        ((CategoryTheory.sheafify J P).map
          (homOfLE (show W₀ ≤ U from le_trans hW₀j (hVU j))).op) s := by
          have hmap :=
            (CategoryTheory.sheafify J P).map_comp
              (homOfLE (hVU j)).op (homOfLE hW₀j).op
          have hcomp :
              (homOfLE (hVU j)).op ≫ (homOfLE hW₀j).op =
                (homOfLE (show W₀ ≤ U from le_trans hW₀j (hVU j))).op := by
            exact Subsingleton.elim _ _
          rw [← ConcreteCategory.comp_apply, ← hmap, hcomp]
  have hηeq :
      ((CategoryTheory.toSheafify J P).app (op W₀)) a =
        ((CategoryTheory.toSheafify J P).app (op W₀)) b := by
    rw [hηa, hηb]
  have hηdiff :
      ((CategoryTheory.toSheafify J P).app (op W₀)) (a - b) = 0 := by
    calc
      ((CategoryTheory.toSheafify J P).app (op W₀)) (a - b)
          =
        ((CategoryTheory.toSheafify J P).app (op W₀)) a -
          ((CategoryTheory.toSheafify J P).app (op W₀)) b := by
          exact map_sub
            (ConcreteCategory.hom ((CategoryTheory.toSheafify J P).app (op W₀))) a b
      _ = 0 := by
          rw [hηeq, sub_self]
  rcases
    addCommGrp_toSheafify_eq_zero_locally
      (X := X) P (U := W₀) (a - b) hηdiff x hxW₀ with
    ⟨W, hWW₀, hxW, habW⟩
  have hWi : W ≤ V i := le_trans hWW₀ hW₀i
  have hWj : W ≤ V j := le_trans hWW₀ hW₀j
  refine ⟨W, hWi, hWj, hxW, ?_⟩
  have habW' :
      P.map (homOfLE hWW₀).op a -
        P.map (homOfLE hWW₀).op b = 0 := by
    simpa [map_sub] using habW
  have habEq :
      P.map (homOfLE hWW₀).op a =
        P.map (homOfLE hWW₀).op b := sub_eq_zero.mp habW'
  have hleft :
      P.map (homOfLE hWi).op (t i) =
        P.map (homOfLE hWW₀).op a := by
    change
      (ConcreteCategory.hom (P.map (homOfLE hWi).op)) (t i) =
        (ConcreteCategory.hom (P.map (homOfLE hWW₀).op))
          ((ConcreteCategory.hom (P.map (homOfLE hW₀i).op)) (t i))
    have hcomp :
        (homOfLE hW₀i).op ≫ (homOfLE hWW₀).op =
          (homOfLE hWi).op := by
      exact Subsingleton.elim _ _
    calc
      (ConcreteCategory.hom (P.map (homOfLE hWi).op)) (t i)
          =
        (ConcreteCategory.hom
          (P.map ((homOfLE hW₀i).op ≫ (homOfLE hWW₀).op))) (t i) := by
          rw [hcomp]
      _ =
        (ConcreteCategory.hom (P.map (homOfLE hWW₀).op))
          ((ConcreteCategory.hom (P.map (homOfLE hW₀i).op)) (t i)) := by
          rw [P.map_comp]
          rfl
  have hright :
      P.map (homOfLE hWW₀).op b =
        P.map (homOfLE hWj).op (t j) := by
    change
      (ConcreteCategory.hom (P.map (homOfLE hWW₀).op))
          ((ConcreteCategory.hom (P.map (homOfLE hW₀j).op)) (t j)) =
        (ConcreteCategory.hom (P.map (homOfLE hWj).op)) (t j)
    have hcomp :
        (homOfLE hW₀j).op ≫ (homOfLE hWW₀).op =
          (homOfLE hWj).op := by
      exact Subsingleton.elim _ _
    calc
      (ConcreteCategory.hom (P.map (homOfLE hWW₀).op))
          ((ConcreteCategory.hom (P.map (homOfLE hW₀j).op)) (t j))
          =
        (ConcreteCategory.hom
          (P.map ((homOfLE hW₀j).op ≫ (homOfLE hWW₀).op))) (t j) := by
          rw [P.map_comp]
          rfl
      _ = (ConcreteCategory.hom (P.map (homOfLE hWj).op)) (t j) := by
          rw [hcomp]
  calc
    P.map (homOfLE hWi).op (t i)
        = P.map (homOfLE hWW₀).op a := hleft
    _ = P.map (homOfLE hWW₀).op b := habEq
    _ = P.map (homOfLE hWj).op (t j) := hright

/--
%%handwave
name:
  Sheafified singular cochains are determined locally
statement:
  Two sections over an open set of the sheafified degree-\(p\) singular
  cochain sheaf are equal if they agree after restriction to a neighborhood
  of every point.
proof:
  Apply separatedness of the sheafification as a sheaf on the usual
  Grothendieck topology of open subsets.
-/
theorem realSingularCochainOpenPresheafComplex_sheafified_section_eq_of_locally_eq
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (p : ℕ) {U : Opens X}
    {s t :
      (CategoryTheory.sheafify
        (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).X p)).obj (op U)}
    (hst :
      ∀ x : X, x ∈ U →
        ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
          (CategoryTheory.sheafify
            (Opens.grothendieckTopology X)
            ((realSingularCochainOpenPresheafComplex X).X p)).map
              (homOfLE hVU).op s =
            (CategoryTheory.sheafify
              (Opens.grothendieckTopology X)
              ((realSingularCochainOpenPresheafComplex X).X p)).map
                (homOfLE hVU).op t) :
    s = t := by
  let J := Opens.grothendieckTopology X
  let P : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X p
  exact
    TopCat.Presheaf.IsSheaf.section_ext
      (F := CategoryTheory.sheafify J P)
      (((presheafToSheaf J AddCommGrpCat.{v}).obj P).property)
      (by
        intro x hxU
        simpa [J, P] using hst x hxU)











/--
%%handwave
name:
  Local singular simplices with the same ambient image lift to the intersection
statement:
  Let \(A\) and \(B\) be open subsets of an open set \(U\).  If a singular
  simplex in \(A\) and a singular simplex in \(B\) have the same image in
  \(U\), then there is a singular simplex in \(A\cap B\) whose images in
  \(A\) and \(B\) are the two given simplices.
proof:
  View the two singular simplices as continuous maps into the corresponding
  open subspaces.  Equality after inclusion into \(U\) says that their
  underlying maps into the ambient space are equal.  Hence the common map has
  image in both \(A\) and \(B\), so it factors through \(A\cap B\).
-/
theorem openSingularSimplex_exists_lift_inf_of_map_eq
    (X : TopCat.{v}) (p : ℕ)
    {U A B : Opens X} (hAU : A ≤ U) (hBU : B ≤ U)
    (σA : openSingularSimplex X p A)
    (σB : openSingularSimplex X p B)
    (hσ :
      openSingularSimplexMap X p hAU σA =
        openSingularSimplexMap X p hBU σB) :
    ∃ σAB : openSingularSimplex X p (A ⊓ B),
      openSingularSimplexMap X p
          (show A ⊓ B ≤ A from inf_le_left) σAB = σA ∧
        openSingularSimplexMap X p
          (show A ⊓ B ≤ B from inf_le_right) σAB = σB := by
  let n : SimplexCategoryᵒᵖ := op (SimplexCategory.mk p)
  let cA := TopCat.toSSetObjEquiv ((Opens.toTopCat X).obj A) n σA
  let cB := TopCat.toSSetObjEquiv ((Opens.toTopCat X).obj B) n σB
  have hcont :
      ((Opens.toTopCat X).map (homOfLE hAU)).hom.comp cA =
        ((Opens.toTopCat X).map (homOfLE hBU)).hom.comp cB := by
    have hU :=
      congrArg
        (TopCat.toSSetObjEquiv ((Opens.toTopCat X).obj U) n) hσ
    calc
      ((Opens.toTopCat X).map (homOfLE hAU)).hom.comp cA
          =
        TopCat.toSSetObjEquiv ((Opens.toTopCat X).obj U) n
          (openSingularSimplexMap X p hAU σA) := by
          simpa [n, cA, openSingularSimplexMap] using
            (toSSetObjEquiv_map_apply
              ((Opens.toTopCat X).map (homOfLE hAU)) p σA).symm
      _ =
        TopCat.toSSetObjEquiv ((Opens.toTopCat X).obj U) n
          (openSingularSimplexMap X p hBU σB) := hU
      _ =
        ((Opens.toTopCat X).map (homOfLE hBU)).hom.comp cB := by
          simpa [n, cB, openSingularSimplexMap] using
            toSSetObjEquiv_map_apply
              ((Opens.toTopCat X).map (homOfLE hBU)) p σB
  let cAB : C(stdSimplex ℝ (Fin (n.unop.len + 1)),
      ((Opens.toTopCat X).obj (A ⊓ B))) :=
    { toFun := fun x =>
        ⟨(cA x).1, ⟨(cA x).2, by
          have hxU :=
            congrArg
              (fun f : C(stdSimplex ℝ (Fin (n.unop.len + 1)),
                  ((Opens.toTopCat X).obj U)) => f x) hcont
          have hxX : (cA x).1 = (cB x).1 := by
            exact congrArg
              (fun z : ((Opens.toTopCat X).obj U) => z.1) hxU
          exact hxX.symm ▸ (cB x).2⟩⟩
      continuous_toFun := by
        exact (continuous_subtype_val.comp cA.continuous).subtype_mk _ }
  let σAB : openSingularSimplex X p (A ⊓ B) :=
    (TopCat.toSSetObjEquiv ((Opens.toTopCat X).obj (A ⊓ B)) n).symm cAB
  refine ⟨σAB, ?_, ?_⟩
  · apply (TopCat.toSSetObjEquiv ((Opens.toTopCat X).obj A) n).injective
    calc
      TopCat.toSSetObjEquiv ((Opens.toTopCat X).obj A) n
          (openSingularSimplexMap X p
            (show A ⊓ B ≤ A from inf_le_left) σAB)
          =
        ((Opens.toTopCat X).map
          (homOfLE (show A ⊓ B ≤ A from inf_le_left))).hom.comp cAB := by
          simpa [n, σAB, openSingularSimplexMap] using
            toSSetObjEquiv_map_apply
              ((Opens.toTopCat X).map
                (homOfLE (show A ⊓ B ≤ A from inf_le_left))) p σAB
      _ = cA := by
          ext x
          apply Subtype.ext
          change (cAB x).1 = (cA x).1
          rfl
  · apply (TopCat.toSSetObjEquiv ((Opens.toTopCat X).obj B) n).injective
    calc
      TopCat.toSSetObjEquiv ((Opens.toTopCat X).obj B) n
          (openSingularSimplexMap X p
            (show A ⊓ B ≤ B from inf_le_right) σAB)
          =
        ((Opens.toTopCat X).map
          (homOfLE (show A ⊓ B ≤ B from inf_le_right))).hom.comp cAB := by
          simpa [n, σAB, openSingularSimplexMap] using
            toSSetObjEquiv_map_apply
              ((Opens.toTopCat X).map
                (homOfLE (show A ⊓ B ≤ B from inf_le_right))) p σAB
      _ = cB := by
          ext x
          have hxU :=
            congrArg
              (fun f : C(stdSimplex ℝ (Fin (n.unop.len + 1)),
                  ((Opens.toTopCat X).obj U)) => f x) hcont
          have hxX : (cA x).1 = (cB x).1 := by
            exact congrArg
              (fun z : ((Opens.toTopCat X).obj U) => z.1) hxU
          apply Subtype.ext
          change (cAB x).1 = (cB x).1
          exact hxX

/--
%%handwave
name:
  Pairwise compatible cochains give the same value to local simplices with the same ambient image
statement:
  Suppose singular cochains on two open subsets agree after restriction to
  their intersection.  If a singular simplex in the first open subset and a
  singular simplex in the second open subset have the same image in a larger
  open set, then the two local cochains have the same value on those
  simplices.
proof:
  The common ambient image factors through the intersection of the two open
  subsets.  Evaluating the equality of the restricted cochains on this
  intersection simplex gives the desired equality of the two local values.
-/
theorem realSingularCochainOpenPresheafComplex_pairwiseCompatible_simplex_eval_eq_of_same_global_image
    (X : TopCat.{v})
    (p : ℕ) (U : Opens X)
    {κ : Type v}
    (W : κ → Opens X)
    (hWU : ∀ a : κ, W a ≤ U)
    (τ : ∀ a : κ,
      ((realSingularCochainOpenPresheafComplex X).X p).obj (op (W a)))
    (hpair :
      ∀ a b : κ,
        ((realSingularCochainOpenPresheafComplex X).X p).map
            (homOfLE (show W a ⊓ W b ≤ W a from inf_le_left)).op (τ a) =
          ((realSingularCochainOpenPresheafComplex X).X p).map
            (homOfLE (show W a ⊓ W b ≤ W b from inf_le_right)).op (τ b))
    {a b : κ}
    (σa : (TopCat.toSSet.obj ((Opens.toTopCat X).obj (W a))).obj
      (op (SimplexCategory.mk p)))
    (σb : (TopCat.toSSet.obj ((Opens.toTopCat X).obj (W b))).obj
      (op (SimplexCategory.mk p)))
    (hσ :
      ((TopCat.toSSet.map
        ((Opens.toTopCat X).map (homOfLE (hWU a)))).app
        (op (SimplexCategory.mk p))) σa =
      ((TopCat.toSSet.map
        ((Opens.toTopCat X).map (homOfLE (hWU b)))).app
        (op (SimplexCategory.mk p))) σb) :
    Sigma.ι
        (fun _ :
            (TopCat.toSSet.obj ((Opens.toTopCat X).obj (W a))).obj
              (op (SimplexCategory.mk p)) =>
          SingularCohomologyCoefficient.{0, v} ℝ) σa ≫
        (singularChainsDegreeCoproductIso
          ((Opens.toTopCat X).obj (W a)) p).inv ≫
        τ a =
      Sigma.ι
        (fun _ :
            (TopCat.toSSet.obj ((Opens.toTopCat X).obj (W b))).obj
              (op (SimplexCategory.mk p)) =>
          SingularCohomologyCoefficient.{0, v} ℝ) σb ≫
        (singularChainsDegreeCoproductIso
          ((Opens.toTopCat X).obj (W b)) p).inv ≫
        τ b := by
  rcases
    openSingularSimplex_exists_lift_inf_of_map_eq
      (X := X) (p := p) (U := U) (A := W a) (B := W b)
      (hAU := hWU a) (hBU := hWU b) σa σb
      (by
        simpa [openSingularSimplexMap] using hσ) with
    ⟨σab, hσa, hσb⟩
  change
    openSingularCochainSimplexEval X p (W a) (τ a) σa =
      openSingularCochainSimplexEval X p (W b) (τ b) σb
  let I : Opens X := W a ⊓ W b
  let P : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X p
  have heqRestricted :
      openSingularCochainSimplexEval X p I
          (P.map
            (homOfLE (show I ≤ W a from inf_le_left)).op (τ a)) σab =
        openSingularCochainSimplexEval X p I
          (P.map
            (homOfLE (show I ≤ W b from inf_le_right)).op (τ b)) σab := by
    rw [hpair a b]
  have hleft :
      openSingularCochainSimplexEval X p I
          (P.map
            (homOfLE (show I ≤ W a from inf_le_left)).op (τ a)) σab =
        openSingularCochainSimplexEval X p (W a) (τ a)
          (openSingularSimplexMap X p
            (show I ≤ W a from inf_le_left) σab) := by
    have hpull :=
      singularCochain_eval_pullback
        (T := ((Opens.toTopCat X).obj I))
        (S := ((Opens.toTopCat X).obj (W a))) p
        ((Opens.toTopCat X).map
          (homOfLE (show I ≤ W a from inf_le_left)))
        (τ a) σab
    simpa [P, I, openSingularCochainSimplexEval, openSingularSimplexMap,
      realSingularCochainOpenPresheafComplex,
      realSingularCochainOpenComplexFunctor,
      realSingularCochainOpenModuleComplexFunctor,
      realSingularCochainModuleComplexFunctor,
      realSingularCochainComplexAddFunctor] using hpull
  have hright :
      openSingularCochainSimplexEval X p I
          (P.map
            (homOfLE (show I ≤ W b from inf_le_right)).op (τ b)) σab =
        openSingularCochainSimplexEval X p (W b) (τ b)
          (openSingularSimplexMap X p
            (show I ≤ W b from inf_le_right) σab) := by
    have hpull :=
      singularCochain_eval_pullback
        (T := ((Opens.toTopCat X).obj I))
        (S := ((Opens.toTopCat X).obj (W b))) p
        ((Opens.toTopCat X).map
          (homOfLE (show I ≤ W b from inf_le_right)))
        (τ b) σab
    simpa [P, I, openSingularCochainSimplexEval, openSingularSimplexMap,
      realSingularCochainOpenPresheafComplex,
      realSingularCochainOpenComplexFunctor,
      realSingularCochainOpenModuleComplexFunctor,
      realSingularCochainModuleComplexFunctor,
      realSingularCochainComplexAddFunctor] using hpull
  calc
    openSingularCochainSimplexEval X p (W a) (τ a) σa
        =
      openSingularCochainSimplexEval X p (W a) (τ a)
        (openSingularSimplexMap X p
          (show I ≤ W a from inf_le_left) σab) := by
          rw [hσa]
    _ =
      openSingularCochainSimplexEval X p I
        (P.map
          (homOfLE (show I ≤ W a from inf_le_left)).op (τ a)) σab := hleft.symm
    _ =
      openSingularCochainSimplexEval X p I
        (P.map
          (homOfLE (show I ≤ W b from inf_le_right)).op (τ b)) σab := heqRestricted
    _ =
      openSingularCochainSimplexEval X p (W b) (τ b)
        (openSingularSimplexMap X p
          (show I ≤ W b from inf_le_right) σab) := hright
    _ =
      openSingularCochainSimplexEval X p (W b) (τ b) σb := by
          rw [hσb]

/--
%%handwave
name:
  Pairwise compatible singular cochains determine global simplex values
statement:
  If ordinary singular cochains on an open cover agree on all pairwise
  intersections, then there is an ordinary singular cochain on the whole open
  set whose value on every singular simplex contained in a cover member is
  the value prescribed by that member.
proof:
  A singular cochain is a linear functional on the free real vector space
  generated by singular simplices.  For a simplex contained in at least one
  cover member, choose one such member and use its prescribed value; pairwise
  compatibility makes this independent of the chosen member.  Give arbitrary
  values to the remaining simplices and extend linearly.
-/
theorem realSingularCochainOpenPresheafComplex_exists_global_simplex_value_of_pairwiseCompatible
    (X : TopCat.{v})
    (p : ℕ) (U : Opens X)
    {κ : Type v}
    (W : κ → Opens X)
    (hWU : ∀ a : κ, W a ≤ U)
    (τ : ∀ a : κ,
      ((realSingularCochainOpenPresheafComplex X).X p).obj (op (W a)))
    (hpair :
      ∀ a b : κ,
        ((realSingularCochainOpenPresheafComplex X).X p).map
            (homOfLE (show W a ⊓ W b ≤ W a from inf_le_left)).op (τ a) =
          ((realSingularCochainOpenPresheafComplex X).X p).map
            (homOfLE (show W a ⊓ W b ≤ W b from inf_le_right)).op (τ b)) :
    ∃ φ :
      ∀ _ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).obj
          (op (SimplexCategory.mk p)),
        SingularCohomologyCoefficient.{0, v} ℝ ⟶
          SingularCohomologyCoefficient.{0, v} ℝ,
      ∀ (a : κ)
        (σ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj (W a))).obj
          (op (SimplexCategory.mk p))),
        φ
            (((TopCat.toSSet.map
              ((Opens.toTopCat X).map (homOfLE (hWU a)))).app
              (op (SimplexCategory.mk p))) σ) =
          Sigma.ι
            (fun _ :
                (TopCat.toSSet.obj ((Opens.toTopCat X).obj (W a))).obj
                  (op (SimplexCategory.mk p)) =>
              SingularCohomologyCoefficient.{0, v} ℝ) σ ≫
            (singularChainsDegreeCoproductIso
              ((Opens.toTopCat X).obj (W a)) p).inv ≫
            τ a := by
  classical
  let Simplex (O : Opens X) :=
    (TopCat.toSSet.obj ((Opens.toTopCat X).obj O)).obj
      (op (SimplexCategory.mk p))
  let EndCoeff :=
    SingularCohomologyCoefficient.{0, v} ℝ ⟶
      SingularCohomologyCoefficient.{0, v} ℝ
  let mapToU (a : κ) : Simplex (W a) → Simplex U :=
    ((TopCat.toSSet.map ((Opens.toTopCat X).map (homOfLE (hWU a)))).app
      (op (SimplexCategory.mk p)))
  let evalLocal (a : κ) (σ : Simplex (W a)) : EndCoeff :=
    Sigma.ι
        (fun _ : Simplex (W a) =>
          SingularCohomologyCoefficient.{0, v} ℝ) σ ≫
      (singularChainsDegreeCoproductIso
        ((Opens.toTopCat X).obj (W a)) p).inv ≫
      τ a
  let Rep (σ : Simplex U) : Type v :=
    Σ a : κ, {σa : Simplex (W a) // mapToU a σa = σ}
  let evalRep : ∀ {σ : Simplex U}, Rep σ → EndCoeff :=
    fun {_} r => evalLocal r.1 r.2.1
  let φ : ∀ σ : Simplex U, EndCoeff :=
    fun σ => if h : Nonempty (Rep σ) then evalRep (Classical.choice h) else 0
  refine ⟨φ, ?_⟩
  intro a σ
  let σU : Simplex U := mapToU a σ
  have hrep : Nonempty (Rep σU) := ⟨⟨a, ⟨σ, rfl⟩⟩⟩
  change φ σU = evalLocal a σ
  dsimp [φ]
  rw [dif_pos hrep]
  let r : Rep σU := Classical.choice hrep
  have hr : mapToU r.1 r.2.1 = mapToU a σ := by
    simpa [σU] using r.2.2
  have hind :=
    realSingularCochainOpenPresheafComplex_pairwiseCompatible_simplex_eval_eq_of_same_global_image
      (X := X) (p := p) (U := U) (W := W) (hWU := hWU)
      (τ := τ) (hpair := hpair) (a := r.1) (b := a)
      (σa := r.2.1) (σb := σ)
      (hσ := by
        simpa [mapToU] using hr)
  simpa [evalLocal] using hind

/--
%%handwave
name:
  Pairwise compatible singular cochains have a global cochain with prescribed simplex values
statement:
  If ordinary singular cochains on an open cover agree on all pairwise
  intersections, then there is an ordinary singular cochain on the whole open
  set whose value on every singular simplex contained in a cover member is
  the value prescribed by that member.
proof:
  First use compatibility on overlaps to obtain a well-defined value for each
  singular simplex of the whole open set that is represented in a cover
  member.  Extend this assignment linearly over the free real vector space on
  singular simplices.  Naturality of pullback identifies the values after
  restriction to each cover member.
-/
theorem realSingularCochainOpenPresheafComplex_exists_global_cochain_simplex_eval_eq_of_pairwiseCompatible
    (X : TopCat.{v})
    (p : ℕ) (U : Opens X)
    {κ : Type v}
    (W : κ → Opens X)
    (hWU : ∀ a : κ, W a ≤ U)
    (τ : ∀ a : κ,
      ((realSingularCochainOpenPresheafComplex X).X p).obj (op (W a)))
    (hpair :
      ∀ a b : κ,
        ((realSingularCochainOpenPresheafComplex X).X p).map
            (homOfLE (show W a ⊓ W b ≤ W a from inf_le_left)).op (τ a) =
          ((realSingularCochainOpenPresheafComplex X).X p).map
            (homOfLE (show W a ⊓ W b ≤ W b from inf_le_right)).op (τ b)) :
    ∃ T : ((realSingularCochainOpenPresheafComplex X).X p).obj (op U),
      ∀ (a : κ)
        (σ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj (W a))).obj
          (op (SimplexCategory.mk p))),
        Sigma.ι
            (fun _ :
                (TopCat.toSSet.obj ((Opens.toTopCat X).obj (W a))).obj
                  (op (SimplexCategory.mk p)) =>
              SingularCohomologyCoefficient.{0, v} ℝ) σ ≫
            (singularChainsDegreeCoproductIso
              ((Opens.toTopCat X).obj (W a)) p).inv ≫
            ((realSingularCochainOpenPresheafComplex X).X p).map
              (homOfLE (hWU a)).op T =
          Sigma.ι
            (fun _ :
                (TopCat.toSSet.obj ((Opens.toTopCat X).obj (W a))).obj
                  (op (SimplexCategory.mk p)) =>
              SingularCohomologyCoefficient.{0, v} ℝ) σ ≫
            (singularChainsDegreeCoproductIso
              ((Opens.toTopCat X).obj (W a)) p).inv ≫
            τ a := by
  rcases
    realSingularCochainOpenPresheafComplex_exists_global_simplex_value_of_pairwiseCompatible
      (X := X) (p := p) (U := U) (W := W) (hWU := hWU)
      (τ := τ) (hpair := hpair) with
    ⟨φ, hφ⟩
  let T :
      (SingularCochainComplex ℝ ((Opens.toTopCat X).obj U)).X p :=
    singularCochainOfSimplexEnd ((Opens.toTopCat X).obj U) p φ
  refine ⟨T, ?_⟩
  intro a σ
  have hpull :=
    singularCochain_eval_pullback
      (T := ((Opens.toTopCat X).obj (W a)))
      (S := ((Opens.toTopCat X).obj U)) p
      ((Opens.toTopCat X).map (homOfLE (hWU a))) T σ
  have heval :=
    singularCochainOfSimplexEnd_eval ((Opens.toTopCat X).obj U) p φ
      (((TopCat.toSSet.map
        ((Opens.toTopCat X).map (homOfLE (hWU a)))).app
        (op (SimplexCategory.mk p))) σ)
  calc
    Sigma.ι
          (fun _ :
              (TopCat.toSSet.obj ((Opens.toTopCat X).obj (W a))).obj
                (op (SimplexCategory.mk p)) =>
            SingularCohomologyCoefficient.{0, v} ℝ) σ ≫
        (singularChainsDegreeCoproductIso
          ((Opens.toTopCat X).obj (W a)) p).inv ≫
        ((realSingularCochainOpenPresheafComplex X).X p).map
          (homOfLE (hWU a)).op T
        =
      Sigma.ι
          (fun _ :
              (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).obj
                (op (SimplexCategory.mk p)) =>
            SingularCohomologyCoefficient.{0, v} ℝ)
          (((TopCat.toSSet.map
            ((Opens.toTopCat X).map (homOfLE (hWU a)))).app
            (op (SimplexCategory.mk p))) σ) ≫
        (singularChainsDegreeCoproductIso
          ((Opens.toTopCat X).obj U) p).inv ≫ T := by
          simpa [T, realSingularCochainOpenPresheafComplex,
            realSingularCochainOpenComplexFunctor,
            realSingularCochainOpenModuleComplexFunctor,
            realSingularCochainModuleComplexFunctor,
            realSingularCochainComplexAddFunctor] using hpull
    _ = φ
          (((TopCat.toSSet.map
            ((Opens.toTopCat X).map (homOfLE (hWU a)))).app
            (op (SimplexCategory.mk p))) σ) := by
          simpa [T] using heval
    _ =
      Sigma.ι
          (fun _ :
              (TopCat.toSSet.obj ((Opens.toTopCat X).obj (W a))).obj
                (op (SimplexCategory.mk p)) =>
            SingularCohomologyCoefficient.{0, v} ℝ) σ ≫
        (singularChainsDegreeCoproductIso
          ((Opens.toTopCat X).obj (W a)) p).inv ≫
        τ a := hφ a σ

/--
%%handwave
name:
  Pairwise compatible singular cochains glue to a global cochain
statement:
  If ordinary singular cochains on an open cover agree on all pairwise
  intersections, then there is an ordinary singular cochain on the whole open
  set whose restriction to every member of the cover is the prescribed local
  cochain.
proof:
  A singular cochain is a linear functional on the free real vector space
  generated by singular simplices.  On a simplex whose image lies in one
  member of the cover, use the value of that member's local cochain; pairwise
  compatibility makes this independent of the chosen member.  On remaining
  simplices choose arbitrary values, and extend linearly.
-/
theorem realSingularCochainOpenPresheafComplex_exists_global_cochain_of_pairwiseCompatible
    (X : TopCat.{v})
    (p : ℕ) (U : Opens X)
    {κ : Type v}
    (W : κ → Opens X)
    (hWU : ∀ a : κ, W a ≤ U)
    (τ : ∀ a : κ,
      ((realSingularCochainOpenPresheafComplex X).X p).obj (op (W a)))
    (hpair :
      ∀ a b : κ,
        ((realSingularCochainOpenPresheafComplex X).X p).map
            (homOfLE (show W a ⊓ W b ≤ W a from inf_le_left)).op (τ a) =
          ((realSingularCochainOpenPresheafComplex X).X p).map
            (homOfLE (show W a ⊓ W b ≤ W b from inf_le_right)).op (τ b)) :
    ∃ T : ((realSingularCochainOpenPresheafComplex X).X p).obj (op U),
      ∀ a : κ,
        ((realSingularCochainOpenPresheafComplex X).X p).map
            (homOfLE (hWU a)).op T = τ a := by
  rcases
    realSingularCochainOpenPresheafComplex_exists_global_cochain_simplex_eval_eq_of_pairwiseCompatible
      (X := X) (p := p) (U := U) (W := W) (hWU := hWU)
      (τ := τ) (hpair := hpair) with
    ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro a
  apply realSingularCochainOpenPresheafComplex_eq_of_forall_simplex_eval_eq
  intro σ
  exact hT a σ










/--
%%handwave
name:
  Locally zero positive-degree classes have local boundary representatives
statement:
  If a positive-degree singular cochain cycle on the whole space has locally
  zero ordinary singular cohomology class, then locally the restricted cycle
  is an ordinary coboundary.
proof:
  On each neighborhood where the restricted cohomology class is zero, use the
  quotient map from cycles to cohomology to choose a cochain primitive.
-/
theorem openSingularCochainTopCycleLocallyBoundary_of_locallyZero_succ
    (X : TopCat.{v})
    (m : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles (m + 1))
    (hz : openSingularCochainTopCycleLocallyZero X (m + 1) z) :
    openSingularCochainTopCycleLocallyBoundary X m z := by
  intro x
  rcases hz x with ⟨U, hxU, hzU⟩
  rcases
    cochainComplex_addCommGrp_exists_preimage_of_homologyπ_eq_zero
      (K := (realSingularCochainOpenComplexFunctor X).obj (op U))
      m ((openSingularCochainTopRestrictCycle X U (m + 1)) z) hzU with
    ⟨β, hβ⟩
  exact ⟨U, hxU, β, hβ⟩




















/--
%%handwave
name:
  The top-open sheafification-unit comparison respects scalars on cohomology
statement:
  On cohomology, the map from top-open singular cochains to global
  sheafified singular cochains commutes with multiplication by any real
  scalar.
proof:
  This follows from naturality of the sheafification unit and of the
  identification of global sections with sections over the terminal open set,
  applied to the scalar-multiplication endomorphism of the singular-cochain
  presheaf.
-/
theorem openSingularCochainTopToSheafifiedGlobalSections_homology_scalar
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (r : ℝ) (n : ℕ) :
    HomologicalComplex.homologyMap
        (openSingularCochainTopToSheafifiedGlobalSections X) n ≫
      HomologicalComplex.homologyMap
        (((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
            (sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r)) n =
    HomologicalComplex.homologyMap
        ((realSingularCochainOpenComplexFunctorScalarNatTrans X r).app
          (op (⊤ : Opens X))) n ≫
      HomologicalComplex.homologyMap
        (openSingularCochainTopToSheafifiedGlobalSections X) n := by
  calc
    HomologicalComplex.homologyMap
        (openSingularCochainTopToSheafifiedGlobalSections X) n ≫
      HomologicalComplex.homologyMap
        (((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
            (sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r)) n
        =
      HomologicalComplex.homologyMap
        (openSingularCochainTopToSheafifiedGlobalSections X ≫
          (((Sheaf.Γ (Opens.grothendieckTopology X)
            AddCommGrpCat.{v}).mapHomologicalComplex
            (ComplexShape.up ℕ)).map
              (sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r))) n := by
          rw [HomologicalComplex.homologyMap_comp]
    _ =
      HomologicalComplex.homologyMap
        ((realSingularCochainOpenComplexFunctorScalarNatTrans X r).app
            (op (⊤ : Opens X)) ≫
          openSingularCochainTopToSheafifiedGlobalSections X) n := by
          rw [openSingularCochainTopToSheafifiedGlobalSections_scalar]
    _ =
      HomologicalComplex.homologyMap
        ((realSingularCochainOpenComplexFunctorScalarNatTrans X r).app
          (op (⊤ : Opens X))) n ≫
      HomologicalComplex.homologyMap
        (openSingularCochainTopToSheafifiedGlobalSections X) n := by
          rw [HomologicalComplex.homologyMap_comp]


/--
%%handwave
name:
  Top-open abelian singular-cochain cohomology is ordinary real singular cohomology
statement:
  The cohomology of the abelian-group singular-cochain complex on the top
  open is additively identified with ordinary real singular cohomology of
  that top open, and the identification carries cochain-level scalar
  multiplication to the scalar action on cohomology.
proof:
  The abelian-group complex is obtained from the real-vector-space singular
  cochain complex by forgetting scalar structure.  The forgetful functor
  preserves this homology object, and scalar multiplication is the same map
  before and after forgetting.
-/
theorem realSingularCochainOpenComplexFunctor_top_homology_addEquiv_singularCohomology
    (X : TopCat.{v}) :
    ∀ n : ℕ,
      ∃ e :
        ↥(((realSingularCochainOpenComplexFunctor X).obj
            (op (⊤ : Opens X))).homology n) ≃+
          SingularCohomology ℝ ((Opens.toTopCat X).obj (⊤ : Opens X)) n,
        ∀ (r : ℝ)
          (x : ↥(((realSingularCochainOpenComplexFunctor X).obj
            (op (⊤ : Opens X))).homology n)),
          e ((HomologicalComplex.homologyMap
              ((realSingularCochainOpenComplexFunctorScalarNatTrans X r).app
                (op (⊤ : Opens X))) n) x) =
            r • e x := by
  intro n
  let K : CochainComplex (ModuleCat.{v} ℝ) ℕ :=
    (realSingularCochainOpenModuleComplexFunctor X).obj (op (⊤ : Opens X))
  rcases cochainComplex_forget₂_moduleCat_homology_addEquiv_with_smul
      (K := K) n with
    ⟨e, he⟩
  refine ⟨e, ?_⟩
  intro r x
  simpa [K, realSingularCochainOpenComplexFunctor,
    realSingularCochainOpenComplexFunctorScalarNatTrans] using he r x







/--
%%handwave
name:
  The standard augmentation of the sheafified open singular-cochain complex is exact
statement:
  On a paracompact locally contractible space, the standard augmentation from
  the constant real sheaf to the sheafified open singular-cochain complex
  commutes with the first coboundary, is monic and exact in degree zero, and
  the positive part of the cochain complex is exact.  The augmentation is
  compatible with scalar multiplication.
proof:
  The augmentation sends a locally constant real-valued section to the
  corresponding zero-cochain germ.  Compatibility with the coboundary follows
  because constant zero-cochains have zero coboundary.  Monicity and exactness
  are checked on stalks, using local contractibility to reduce to the
  augmented singular cochain complex after restriction along null-homotopic
  neighborhood inclusions.
-/
theorem exists_sheafifiedOpenRealSingularCochainSheafAugmentation_with_resolution_properties
    (X : TopCat.{v})
    [ParacompactSpace X] (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] :
    ∃ (ε : RealConstantAddSheaf X ⟶ (realSingularCochainSheafComplex X).X 0)
      (hε : ε ≫ (realSingularCochainSheafComplex X).d 0 1 = 0),
      (∀ r : ℝ,
        ε ≫
            (sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r).f 0 =
          realConstantSheafScalarEnd X r ≫ ε) ∧
      ({ f := ε, g := (realSingularCochainSheafComplex X).d 0 1, zero := hε } :
        ShortComplex
          (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})).Exact ∧
      Mono ε ∧
      (∀ m : ℕ, (realSingularCochainSheafComplex X).ExactAt (m + 1)) := by
  rcases exists_sheafifiedOpenRealSingularCochainSheafAugmentationData_with_exactness
      (X := X) hloc with
    ⟨A, hexact_zero, hmono_ε, hexact_pos⟩
  exact
    ⟨A.ε, A.hε, A.scalar_augmentation, hexact_zero, hmono_ε, hexact_pos⟩

/--
%%handwave
name:
  Injective chain maps give surjective cochain pullbacks
statement:
  If the map induced on singular \(p\)-chains by a continuous map is
  injective, then pullback of real singular \(p\)-cochains along that map is
  surjective.
proof:
  A \(p\)-cochain is a linear functional on \(p\)-chains.  Since real vector
  spaces are injective modules over \(\mathbb R\), any functional on the
  domain of an injective linear map extends across that map.
-/
theorem singularCochainMap_epi_of_singularChains_map_injective
    {T S : TopCat.{v}} (f : T ⟶ S) (p : ℕ)
    (hinj : Function.Injective
      (ModuleCat.Hom.hom
        ((((AlgebraicTopology.singularChainComplexFunctor
              (ModuleCat.{v} ℝ)).obj
            (SingularCohomologyCoefficient.{0, v} ℝ)).map f).f p))) :
    Epi ((singularCochainMap ℝ f).f p) := by
  rw [ModuleCat.epi_iff_surjective]
  intro α
  let chainMap : (SingularChains ℝ T).X p →ₗ[ℝ] (SingularChains ℝ S).X p :=
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor
            (ModuleCat.{v} ℝ)).obj
          (SingularCohomologyCoefficient.{0, v} ℝ)).map f).f p)
  letI : Module.Injective ℝ (SingularCohomologyCoefficient.{0, v} ℝ) := by
    change Module.Injective ℝ (ULift.{v} ℝ)
    exact Module.injective_of_isSemisimpleRing ℝ (ULift.{v} ℝ)
  let αlin : (SingularChains ℝ T).X p →ₗ[ℝ]
      SingularCohomologyCoefficient.{0, v} ℝ := by
    exact ModuleCat.Hom.hom α
  rcases Module.Injective.extension_property (R := ℝ)
      (M := SingularCohomologyCoefficient.{0, v} ℝ)
      (P := (SingularChains ℝ T).X p)
      (P' := (SingularChains ℝ S).X p)
      chainMap hinj αlin with ⟨β, hβ⟩
  refine ⟨ModuleCat.ofHom β, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show ModuleCat.Hom.hom
      ((ModuleCat.Hom.hom ((singularCochainMap ℝ f).f p) (ModuleCat.ofHom β)) :
        (SingularChains ℝ T).X p ⟶ SingularCohomologyCoefficient.{0, v} ℝ) x =
      αlin x
  unfold singularCochainMap SingularCochainComplex SingularChains ChainComplex.linearYonedaObj
  change (β.comp chainMap) x = αlin x
  exact congrFun (congrArg DFunLike.coe hβ) x

/--
%%handwave
name:
  Open inclusions inject singular chains
statement:
  For an inclusion of open subsets \(V\subset U\), the induced map from real
  singular \(p\)-chains on \(V\) to real singular \(p\)-chains on \(U\) is
  injective.
proof:
  Singular \(p\)-chains are the free real vector space on singular
  \(p\)-simplices.  A simplex in \(V\) is also a simplex in \(U\), and this
  inclusion of bases is injective; the induced linear map on free vector
  spaces is therefore injective.
-/
theorem singularChains_openInclusion_map_injective
    (X : TopCat.{v}) (p : ℕ) :
    ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V),
      Function.Injective
        (ModuleCat.Hom.hom
          ((((AlgebraicTopology.singularChainComplexFunctor
                (ModuleCat.{v} ℝ)).obj
              (SingularCohomologyCoefficient.{0, v} ℝ)).map
                ((Opens.toTopCat X).map i.unop)).f p)) := by
  intro U V i
  let f : ((Opens.toTopCat X).obj (unop V)) ⟶
      ((Opens.toTopCat X).obj (unop U)) :=
    (Opens.toTopCat X).map i.unop
  haveI : Mono f := by
    rw [TopCat.mono_iff_injective]
    intro x y hxy
    exact Subtype.ext (congrArg (fun z => z.1) hxy)
  haveI hSSet : Mono (TopCat.toSSet.map f) := by
    infer_instance
  have happMono : Mono ((TopCat.toSSet.map f).app (op (SimplexCategory.mk p))) :=
    (NatTrans.mono_iff_mono_app _).mp hSSet _
  have hsigma :
      Mono
        (((sigmaConst.{v}.obj (SingularCohomologyCoefficient.{0, v} ℝ)).map
          ((TopCat.toSSet.map f).app (op (SimplexCategory.mk p))))) := by
    infer_instance
  rw [← ModuleCat.mono_iff_injective]
  change
    Mono
      ((((AlgebraicTopology.singularChainComplexFunctor
            (ModuleCat.{v} ℝ)).obj
          (SingularCohomologyCoefficient.{0, v} ℝ)).map f).f p)
  unfold AlgebraicTopology.singularChainComplexFunctor
    SSet.chainComplexFunctor
  simpa [f, AlgebraicTopology.alternatingFaceMapComplex_map_f] using hsigma

/--
%%handwave
name:
  Open singular cochains have surjective restrictions
statement:
  For an inclusion of open subsets \(V\subset U\), every real singular
  \(p\)-cochain on \(V\) extends to a real singular \(p\)-cochain on \(U\).
proof:
  A singular cochain is a linear functional on the free real module generated
  by singular simplices.  Extend a functional from the singular simplices
  landing in \(V\) to all singular simplices landing in \(U\) by choosing
  value zero on the remaining basis vectors.
-/
theorem realSingularCochainOpenPresheafComplex_restriction_epi
    (X : TopCat.{v}) (p : ℕ) :
    ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V),
      Epi (((realSingularCochainOpenPresheafComplex X).X p).map i) := by
  intro U V i
  have h :
      Epi
        ((singularCochainMap ℝ ((Opens.toTopCat X).map i.unop)).f p) :=
    singularCochainMap_epi_of_singularChains_map_injective
      ((Opens.toTopCat X).map i.unop) p
      (singularChains_openInclusion_map_injective (X := X) p i)
  change Epi (((realSingularCochainOpenComplexFunctor X).map i).f p)
  dsimp [realSingularCochainOpenComplexFunctor,
    realSingularCochainOpenModuleComplexFunctor,
    realSingularCochainComplexAddFunctor,
    realSingularCochainModuleComplexFunctor]
  rw [AddCommGrpCat.epi_iff_surjective]
  exact (ModuleCat.epi_iff_surjective _).mp h

/--
%%handwave
name:
  The abelian-group sheafification map is locally surjective
statement:
  For an abelian-group presheaf on a topological space, every section of the
  associated sheaf is locally represented by a section of the presheaf.
proof:
  This is the standard local description of sheafification: the associated
  sheaf is built from germs of presheaf sections, so every section is locally
  one of those germs.
-/
theorem addCommGrp_toSheafify_isLocallySurjective
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (P : TopCat.Presheaf AddCommGrpCat.{v} X) :
    TopCat.Presheaf.IsLocallySurjective
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) := by
  exact CategoryTheory.Presheaf.isLocallySurjective_toSheafify'
    (J := Opens.grothendieckTopology X) P

/--
%%handwave
name:
  Sheafifying a globally represented flasque abelian presheaf gives a flasque sheaf
statement:
  If an abelian-group presheaf on a topological space has surjective
  restriction maps for every inclusion of open sets, and every section of its
  associated sheaf is represented by a presheaf section on the same open set,
  then its associated sheaf has surjective restriction maps.
proof:
  Use naturality of the sheafification map.  A section over the smaller open
  set is represented by a presheaf section there, that presheaf section
  extends over the larger open set, and naturality identifies the
  sheafification of the extension with the required restricted section.
-/
theorem sheafification_preserves_flasque_addCommGrp_of_toSheafify_app_epi
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (P : TopCat.Presheaf AddCommGrpCat.{v} X)
    (hP : TopCat.Presheaf.IsFlasque P)
    (hunit :
      ∀ U : (Opens X)ᵒᵖ,
        Epi ((CategoryTheory.toSheafify
          (Opens.grothendieckTopology X) P).app U)) :
    TopCat.Sheaf.IsFlasque
      ((presheafToSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{v}).obj P) := by
  let J := Opens.grothendieckTopology X
  let F : Sheaf J AddCommGrpCat.{v} :=
    (presheafToSheaf J AddCommGrpCat.{v}).obj P
  let η : P ⟶ F.obj := CategoryTheory.toSheafify J P
  refine { epi := ?_ }
  intro U V i
  have hcomp : Epi (P.map i ≫ η.app V) := by
    haveI : Epi (P.map i) := hP.epi i
    haveI : Epi (η.app V) := hunit V
    infer_instance
  have hnat :
      η.app U ≫ F.obj.map i = P.map i ≫ η.app V := by
    simp [η]
  haveI : Epi (P.map i ≫ η.app V) := hcomp
  exact epi_of_epi_fac hnat




private noncomputable abbrev sheafSectionGenerator (X : TopCat.{v}) (U : Opens X) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v} :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)

private noncomputable def sheafSectionGeneratorMap (X : TopCat.{v}) {U V : Opens X}
    (f : U ⟶ V) : sheafSectionGenerator X U ⟶ sheafSectionGenerator X V :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).map
    (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free)

private noncomputable def sheafSectionGeneratorHomEquiv (X : TopCat.{v}) (U : Opens X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}) :
    (sheafSectionGenerator X U ⟶ F) ≃ F.obj.obj (op U) := by
  let J := Opens.grothendieckTopology X
  let e₁ : (sheafSectionGenerator X U ⟶ F) ≃
      (yoneda.obj U ⋙ AddCommGrpCat.free ⟶ F.obj) :=
    (sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ _
  let e₂ : (yoneda.obj U ⋙ AddCommGrpCat.free ⟶ F.obj) ≃
      (yoneda.obj U ⟶ F.obj ⋙ forget AddCommGrpCat.{v}) :=
    ((AddCommGrpCat.adj).whiskerRight (Opens X)ᵒᵖ).homEquiv _ _
  exact e₁.trans (e₂.trans CategoryTheory.yonedaEquiv)

private lemma sheafSectionGeneratorHomEquiv_map (X : TopCat.{v}) {U V : Opens X}
    (f : U ⟶ V) (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})
    (g : sheafSectionGenerator X V ⟶ F) :
    sheafSectionGeneratorHomEquiv X U F (sheafSectionGeneratorMap X f ≫ g) =
      F.obj.map f.op (sheafSectionGeneratorHomEquiv X V F g) := by
  let η := Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free
  let e₁U : (sheafSectionGenerator X U ⟶ F) ≃
      (yoneda.obj U ⋙ AddCommGrpCat.free ⟶ F.obj) :=
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{v}).homEquiv _ _
  let e₁V : (sheafSectionGenerator X V ⟶ F) ≃
      (yoneda.obj V ⋙ AddCommGrpCat.free ⟶ F.obj) :=
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{v}).homEquiv _ _
  let e₂U : (yoneda.obj U ⋙ AddCommGrpCat.free ⟶ F.obj) ≃
      (yoneda.obj U ⟶ F.obj ⋙ forget AddCommGrpCat.{v}) :=
    ((AddCommGrpCat.adj).whiskerRight (Opens X)ᵒᵖ).homEquiv _ _
  let e₂V : (yoneda.obj V ⋙ AddCommGrpCat.free ⟶ F.obj) ≃
      (yoneda.obj V ⟶ F.obj ⋙ forget AddCommGrpCat.{v}) :=
    ((AddCommGrpCat.adj).whiskerRight (Opens X)ᵒᵖ).homEquiv _ _
  have h₁ : e₁U (sheafSectionGeneratorMap X f ≫ g) = η ≫ e₁V g := by
    simpa [e₁U, e₁V, sheafSectionGeneratorMap, η] using
      (sheafificationAdjunction (Opens.grothendieckTopology X)
        AddCommGrpCat.{v}).homEquiv_naturality_left η g
  have h₂ : e₂U (η ≫ e₁V g) = yoneda.map f ≫ e₂V (e₁V g) := by
    simpa [e₂U, e₂V, η] using
      (((AddCommGrpCat.adj).whiskerRight (Opens X)ᵒᵖ).homEquiv_naturality_left
        (yoneda.map f) (e₁V g))
  dsimp [sheafSectionGeneratorHomEquiv]
  change yonedaEquiv (e₂U (e₁U (sheafSectionGeneratorMap X f ≫ g))) =
    ((F.obj ⋙ forget AddCommGrpCat.{v}).map f.op) (yonedaEquiv (e₂V (e₁V g)))
  rw [CategoryTheory.yonedaEquiv_naturality]
  congr 1
  exact (congrArg e₂U h₁).trans h₂

/--
%%handwave
name:
  Injective abelian sheaves are flasque
statement:
  An injective sheaf of abelian groups on a topological space is flasque.
proof:
  For each open set, use the sheafified free abelian sheaf generated by that
  open; maps from this generator to \(F\) are naturally the sections of \(F\)
  on the open.  An inclusion \(V\subset U\) gives a monomorphism between the
  corresponding generators.  Injectivity extends the morphism corresponding
  to a section over \(V\), and naturality identifies the extension with a
  preimage under the restriction map.
-/
theorem injectiveSheaf_isFlasque
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})
    [Injective F] :
    TopCat.Sheaf.IsFlasque F := by
  refine ⟨?_⟩
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  let j : sheafSectionGenerator X V.unop ⟶ sheafSectionGenerator X U.unop :=
    sheafSectionGeneratorMap X i.unop
  haveI : Mono j := by
    dsimp [j, sheafSectionGeneratorMap]
    infer_instance
  let gV : sheafSectionGenerator X V.unop ⟶ F :=
    (sheafSectionGeneratorHomEquiv X V.unop F).symm s
  let G : sheafSectionGenerator X U.unop ⟶ F :=
    Injective.factorThru gV j
  refine ⟨sheafSectionGeneratorHomEquiv X U.unop F G, ?_⟩
  have hcomp : j ≫ G = gV := by
    simp [G, j]
  calc
    F.obj.map i (sheafSectionGeneratorHomEquiv X U.unop F G)
        = sheafSectionGeneratorHomEquiv X V.unop F (j ≫ G) := by
            simpa [j] using (sheafSectionGeneratorHomEquiv_map X i.unop F G).symm
    _ = sheafSectionGeneratorHomEquiv X V.unop F gV := by rw [hcomp]
    _ = s := by simp [gV]

/--
%%handwave
name:
  Flasque left terms make global sections right exact
statement:
  If \(0\to A\to B\to C\to0\) is a short exact sequence of sheaves of
  abelian groups and \(A\) is flasque, then
  \(\Gamma(B)\to\Gamma(C)\) is surjective.
proof:
  Apply the standard maximal-extension argument for flasque sheaves, which
  proves surjectivity on sections over every open set, and identify global
  sections with sections over the whole space.
-/
theorem globalSections_map_epi_of_shortExact_of_flasque_left
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})}
    (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque S.X₁] :
    Epi ((Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{v}).map S.g) := by
  let J := Opens.grothendieckTopology X
  let Γ : Sheaf J AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v} :=
    Sheaf.Γ J AddCommGrpCat.{v}
  letI : OrderTop (Opens X) :=
    { top := (⊤ : Opens X)
      le_top := fun _ => by
        intro _ _
        trivial }
  let sectionsTop : Sheaf J AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v} :=
    (CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
      (op (⊤_ (Opens X)))
  let η : Γ ≅ sectionsTop :=
    CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (J := J) (A := AddCommGrpCat.{v})
      (T := (⊤_ (Opens X))) terminalIsTerminal
  have hsections : Epi (sectionsTop.map S.g) := by
    change Epi (S.g.hom.app (op (⊤_ (Opens X))))
    exact TopCat.Sheaf.IsFlasque.epi_of_shortExact
      (X := X) (U := (⊤_ (Opens X))) hS
  have hcomp :
      Epi (η.hom.app S.X₂ ≫ sectionsTop.map S.g) := by
    haveI : Epi (η.hom.app S.X₂) := inferInstance
    haveI : Epi (sectionsTop.map S.g) := hsections
    infer_instance
  have hnat :
      Γ.map S.g ≫ η.hom.app S.X₃ =
        η.hom.app S.X₂ ≫ sectionsTop.map S.g :=
    η.hom.naturality S.g
  have hΓcomp : Epi (Γ.map S.g ≫ η.hom.app S.X₃) := by
    rw [hnat]
    exact hcomp
  exact (epi_comp_iff_of_isIso (Γ.map S.g) (η.hom.app S.X₃)).mp hΓcomp

/--
%%handwave
name:
  Injective abelian sheaves have no positive cohomology
statement:
  An injective sheaf of abelian groups has vanishing positive sheaf
  cohomology.
proof:
  Sheaf cohomology is an Ext group with the sheaf as target.  Positive Ext
  groups with injective target vanish.
-/
theorem sheafCohomology_subsingleton_of_injective
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})
    [Injective F] :
    ∀ q : ℕ, 0 < q → Subsingleton (F.H q) := by
  intro q hq
  cases q with
  | zero =>
      exact (Nat.not_lt_zero 0 hq).elim
  | succ q =>
      change Subsingleton
        (CategoryTheory.Abelian.Ext ((constantSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ))) F (q + 1))
      exact CategoryTheory.Abelian.Ext.subsingleton_of_injective _ F q

/--
%%handwave
name:
  Flasque abelian sheaves are acyclic
statement:
  A flasque abelian sheaf has vanishing positive sheaf cohomology.
proof:
  Embed the flasque sheaf into an injective sheaf.  Injective sheaves are
  flasque, so the quotient is flasque.  In degree one, global sections are
  right exact for a short exact sequence with flasque left term, and the
  low-degree connecting sequence identifies \(H^1\) with the corresponding
  cokernel.  Higher degrees follow by dimension shifting, using the quotient
  and induction.
-/
theorem sheafCohomology_subsingleton_of_flasque
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})
    [TopCat.Sheaf.IsFlasque F] :
    ∀ q : ℕ, 0 < q → Subsingleton (F.H q) := by
  let J := Opens.grothendieckTopology X
  suffices
      ∀ q : ℕ, 0 < q →
        ∀ (G : Sheaf J AddCommGrpCat.{v}), TopCat.Sheaf.IsFlasque G →
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
          let ip : InjectivePresentation G :=
            Classical.choice (EnoughInjectives.presentation G)
          let S : ShortComplex (Sheaf J AddCommGrpCat.{v}) :=
            ShortComplex.mk ip.f (cokernel.π ip.f) (cokernel.condition ip.f)
          have hS : S.ShortExact :=
            { exact := ShortComplex.exact_cokernel ip.f }
          haveI hInjective_middle : Injective S.X₂ := by
            dsimp [S]
            exact ip.injective
          haveI hflasque_left : TopCat.Sheaf.IsFlasque S.X₁ := by
            dsimp [S]
            exact hG
          haveI hflasque_middle : TopCat.Sheaf.IsFlasque S.X₂ := by
            exact injectiveSheaf_isFlasque (X := X) S.X₂
          haveI hflasque_right : TopCat.Sheaf.IsFlasque S.X₃ :=
            TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
          have hmiddle_acyclic :
              ∀ r : ℕ, 0 < r → Subsingleton (S.X₂.H r) :=
            sheafCohomology_subsingleton_of_injective (X := X) S.X₂
          cases q with
          | zero =>
              have hmiddle_one : Subsingleton (S.X₂.H 1) :=
                hmiddle_acyclic 1 (by norm_num)
              rcases
                CategoryTheory.Sheaf.nonempty_globalSections_cokernel_addEquiv_sheafCohomology_one_of_shortExact_middle_acyclic
                    (J := J) hS hmiddle_one with
                ⟨e⟩
              haveI hΓepi :
                  Epi ((Sheaf.Γ J AddCommGrpCat.{v}).map S.g) :=
                globalSections_map_epi_of_shortExact_of_flasque_left
                  (X := X) hS
              have hcoker :
                  IsZero (cokernel ((Sheaf.Γ J AddCommGrpCat.{v}).map S.g)) :=
                isZero_cokernel_of_epi _
              haveI hcoker_subsingleton :
                  Subsingleton (↥(cokernel ((Sheaf.Γ J AddCommGrpCat.{v}).map S.g))) :=
                AddCommGrpCat.subsingleton_of_isZero hcoker
              change Subsingleton (S.X₁.H 1)
              exact
                ⟨fun x y => by
                  apply e.symm.injective
                  exact Subsingleton.elim _ _⟩
          | succ q =>
              have hright :
                  Subsingleton (S.X₃.H (q + 1)) :=
                ih (q + 1) (by omega) (Nat.succ_pos q) S.X₃ inferInstance
              let e :=
                CategoryTheory.Sheaf.sheafCohomology_connecting_addEquiv_of_middle_acyclic_pos
                    (J := J) hS hmiddle_acyclic (q + 1) (Nat.succ_pos q)
              change Subsingleton (S.X₁.H ((q + 1) + 1))
              exact
                ⟨fun x y => by
                  apply e.symm.injective
                  exact Subsingleton.elim _ _⟩












end ConstantSheaf

/--
%%handwave
name:
  Pullback on singular cohomology
statement:
  A continuous map \(f:X\to Y\) induces a homomorphism
  \(H^n(Y;R)\to H^n(X;R)\).
proof:
  Take the map on homology induced by the pullback cochain map.
-/
abbrev singularCohomologyMap (R : Type u) [CommRing R] {X Y : TopCat.{v}}
    (f : X ⟶ Y) (n : ℕ) :
    SingularCohomology R Y n ⟶ SingularCohomology R X n :=
  HomologicalComplex.homologyMap (singularCochainMap R f) n

/--
%%handwave
name:
  Identity pullback on cohomology
statement:
  The map induced by the identity map of a space is the identity on singular
  cohomology.
proof:
  Combine the identity statement for cochain maps with functoriality of
  homology of complexes.
-/
theorem singularCohomologyMap_id (R : Type u) [CommRing R] (X : TopCat.{v})
    (n : ℕ) :
    singularCohomologyMap R (𝟙 X) n = 𝟙 (SingularCohomology R X n) := by
  rw [singularCohomologyMap, singularCochainMap_id]
  exact
    (HomologicalComplex.homologyMap_id
      (K := SingularCochainComplex R X) (i := n))

/--
%%handwave
name:
  Composition of pullbacks on cohomology
statement:
  On singular cohomology, the map induced by a composite \(g\circ f\) is
  \(f^*\circ g^*\).
proof:
  Combine the corresponding statement for cochain maps with functoriality of
  homology of complexes.
-/
theorem singularCohomologyMap_comp (R : Type u) [CommRing R] {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    singularCohomologyMap R (f ≫ g) n =
      singularCohomologyMap R g n ≫ singularCohomologyMap R f n := by
  rw [singularCohomologyMap, singularCochainMap_comp]
  exact
    (HomologicalComplex.homologyMap_comp
      (φ := singularCochainMap R g)
      (ψ := singularCochainMap R f) (i := n))

/--
%%handwave
name:
  Vanishing is inherited by retracts
statement:
  If \(A\) is a retract of \(X\) and \(H^n(X;R)=0\), then \(H^n(A;R)=0\).
proof:
  Let \(i:A\to X\) and \(r:X\to A\) satisfy \(r\circ i=\mathrm{id}_A\).
  Contravariance gives \(i^* r^*=\mathrm{id}_{H^n(A)}\).  Since
  \(H^n(X;R)\) is zero, the factorization through it is the zero map, so the
  identity of \(H^n(A;R)\) is zero.
-/
theorem singularCohomology_isZero_of_retract
    (R : Type u) [CommRing R] {A X : TopCat.{v}}
    (i : A ⟶ X) (r : X ⟶ A) (hret : i ≫ r = 𝟙 A)
    (n : ℕ) (hX : IsZero (SingularCohomology R X n)) :
    IsZero (SingularCohomology R A n) := by
  rw [IsZero.iff_id_eq_zero]
  calc
    𝟙 (SingularCohomology R A n)
        = singularCohomologyMap R (𝟙 A) n := by
          rw [singularCohomologyMap_id]
    _ = singularCohomologyMap R (i ≫ r) n := by rw [hret]
    _ = singularCohomologyMap R r n ≫ singularCohomologyMap R i n := by
          rw [singularCohomologyMap_comp]
    _ = 0 := by
          have hr_zero : singularCohomologyMap R r n = 0 := hX.eq_of_tgt _ _
          rw [hr_zero, zero_comp]

/--
%%handwave
name:
  Zero cohomology is subsingleton
statement:
  If a singular cohomology object is zero, then its underlying module has at
  most one element.
proof:
  Use the characterization of zero objects in the category of modules.
-/
theorem singularCohomology_subsingleton_of_isZero
    (R : Type u) [CommRing R] (X : TopCat.{v}) (n : ℕ)
    (h : IsZero (SingularCohomology R X n)) :
    Subsingleton (SingularCohomology R X n) :=
  (ModuleCat.isZero_iff_subsingleton (M := SingularCohomology R X n)).1 h

private lemma complexShape_symm_next_eq_prev
    {ι : Type*} (c : ComplexShape ι) (i : ι) :
    c.symm.next i = c.prev i := by
  by_cases h : ∃ j, c.Rel j i
  · rcases h with ⟨j, hj⟩
    exact ((c.symm).next_eq' hj).trans ((c.prev_eq' hj).symm)
  · have hprev : c.prev i = i := by
      exact c.prev_eq_self' i (by simpa using h)
    have hnext : c.symm.next i = i := by
      exact (c.symm).next_eq_self' i (by simpa [ComplexShape.symm] using h)
    exact hnext.trans hprev.symm

private lemma complexShape_symm_prev_eq_next
    {ι : Type*} (c : ComplexShape ι) (i : ι) :
    c.symm.prev i = c.next i := by
  simpa using (complexShape_symm_next_eq_prev c.symm i).symm

/--
%%handwave
name:
  Opposite complexes preserve homotopies
statement:
  Passing a homotopy of complexes in an opposite category through the
  opposite-complex equivalence gives a homotopy of the induced maps in the
  original category.
proof:
  Unop the homotopy components and reverse their two degree indices.  The
  homotopy identity is the unop of the original identity, with the two
  boundary terms interchanged.
-/
theorem homotopy_unopFunctor_map_op
    {V : Type*} [Category* V] [Preadditive V] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex Vᵒᵖ c} {f g : K ⟶ L}
    (H : _root_.Homotopy f g) :
    Nonempty
      (_root_.Homotopy
        ((HomologicalComplex.unopFunctor V c).map f.op)
        ((HomologicalComplex.unopFunctor V c).map g.op)) := by
  refine ⟨?_⟩
  refine
    { hom := fun i j => (H.hom j i).unop
      zero := ?_
      comm := ?_ }
  · intro i j hij
    simpa using congrArg Quiver.Hom.unop (H.zero j i hij)
  · intro i
    have h := congrArg Quiver.Hom.unop (H.comm i)
    dsimp [dNext, prevD, fromNext, toPrev] at h ⊢
    change (f.f i).unop =
      ((L.d (c.symm.next i) i).unop ≫
          (H.hom i (c.symm.next i)).unop +
        (H.hom (c.symm.prev i) i).unop ≫
          (K.d i (c.symm.prev i)).unop) +
        (g.f i).unop
    simpa [complexShape_symm_next_eq_prev,
      complexShape_symm_prev_eq_next, unop_add, add_assoc, add_comm, add_left_comm] using h

/--
%%handwave
name:
  Dualizing a singular chain homotopy
statement:
  A chain homotopy between the maps induced on singular chains dualizes to a
  cochain homotopy between the pullback maps on singular cochains.
proof:
  Apply linear Yoneda to the chain homotopy, pass through the opposite-complex
  equivalence, and unop the result.  This is a formal homological-algebra
  statement about dualizing homotopies of complexes.
-/
theorem singularCochainMap_homotopy_of_chainHomotopy
    (R : Type u) [CommRing R] {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (H :
      _root_.Homotopy
        (((AlgebraicTopology.singularChainComplexFunctor
              (ModuleCat.{max u v} R)).obj
            (SingularCohomologyCoefficient.{u, v} R)).map f)
        (((AlgebraicTopology.singularChainComplexFunctor
              (ModuleCat.{max u v} R)).obj
            (SingularCohomologyCoefficient.{u, v} R)).map g)) :
    Nonempty (_root_.Homotopy (singularCochainMap R f) (singularCochainMap R g)) := by
  let F :=
    (((linearYoneda R (ModuleCat.{max u v} R)).obj
      (SingularCohomologyCoefficient.{u, v} R)).rightOp)
  have Hdual :
      _root_.Homotopy
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (((AlgebraicTopology.singularChainComplexFunctor
                (ModuleCat.{max u v} R)).obj
              (SingularCohomologyCoefficient.{u, v} R)).map f))
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (((AlgebraicTopology.singularChainComplexFunctor
                (ModuleCat.{max u v} R)).obj
              (SingularCohomologyCoefficient.{u, v} R)).map g)) :=
    F.mapHomotopy H
  simpa [F, singularCochainMap] using
    homotopy_unopFunctor_map_op
      (V := ModuleCat.{max u v} R)
      (c := ComplexShape.down ℕ)
      Hdual

/--
%%handwave
name:
  Chain homotopy invariance of singular cohomology
statement:
  If the maps induced on singular chains are chain homotopic, then the
  corresponding pullback maps on singular cohomology agree.
proof:
  Dualize the chain homotopy to a cochain homotopy and use the fact that
  homotopic maps of complexes induce the same map on homology.
-/
theorem singularCohomologyMap_eq_of_chainHomotopy
    (R : Type u) [CommRing R] {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (H :
      _root_.Homotopy
        (((AlgebraicTopology.singularChainComplexFunctor
              (ModuleCat.{max u v} R)).obj
            (SingularCohomologyCoefficient.{u, v} R)).map f)
        (((AlgebraicTopology.singularChainComplexFunctor
              (ModuleCat.{max u v} R)).obj
            (SingularCohomologyCoefficient.{u, v} R)).map g))
    (n : ℕ) :
    singularCohomologyMap R f n = singularCohomologyMap R g n := by
  rcases singularCochainMap_homotopy_of_chainHomotopy R H with ⟨h⟩
  exact h.homologyMap_eq n

/--
%%handwave
name:
  Homotopy invariance of singular cohomology
statement:
  Homotopic continuous maps induce the same map on singular cohomology.
proof:
  The topological homotopy gives the standard prism-operator chain homotopy
  on singular chains.  Chain-homotopy invariance of singular cohomology then
  gives the conclusion.
-/
theorem singularCohomologyMap_eq_of_homotopy
    (R : Type u) [CommRing R] {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (n : ℕ) :
    singularCohomologyMap R f n = singularCohomologyMap R g n := by
  exact
    singularCohomologyMap_eq_of_chainHomotopy R
      (H.singularChainComplexFunctorObjMap
        (SingularCohomologyCoefficient.{u, v} R)) n

/--
%%handwave
name:
  Vanishing is inherited across a one-sided homotopy inverse
statement:
  Suppose \(f:X\to Y\) and \(g:Y\to X\) have \(g\circ f\) homotopic to
  \(\mathrm{id}_X\).  If \(H^n(Y;R)=0\), then \(H^n(X;R)=0\).
proof:
  Homotopy invariance identifies the map induced by \(g\circ f\) with the
  identity on \(H^n(X;R)\).  Contravariance writes this map as \(f^*g^*\),
  so the identity factors through the zero object \(H^n(Y;R)\).
-/
theorem singularCohomology_isZero_of_left_homotopy_inverse
    (R : Type u) [CommRing R] {X Y : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ X) (H : TopCat.Homotopy (f ≫ g) (𝟙 X))
    (n : ℕ) (hY : IsZero (SingularCohomology R Y n)) :
    IsZero (SingularCohomology R X n) := by
  rw [IsZero.iff_id_eq_zero]
  calc
    𝟙 (SingularCohomology R X n)
        = singularCohomologyMap R (𝟙 X) n := by
          rw [singularCohomologyMap_id]
    _ = singularCohomologyMap R (f ≫ g) n := by
          rw [← singularCohomologyMap_eq_of_homotopy R H n]
    _ = singularCohomologyMap R g n ≫ singularCohomologyMap R f n := by
          rw [singularCohomologyMap_comp]
    _ = 0 := by
          have hg_zero : singularCohomologyMap R g n = 0 := hY.eq_of_tgt _ _
          rw [hg_zero, zero_comp]

/--
%%handwave
name:
  Homotopy equivalences preserve vanishing singular cohomology
statement:
  If \(X\) is homotopy equivalent to \(Y\) and \(H^n(Y;R)=0\), then
  \(H^n(X;R)=0\).
proof:
  Apply the one-sided homotopy-inverse argument to the two maps which form the
  homotopy equivalence.
-/
theorem singularCohomology_isZero_of_homotopyEquiv
    (R : Type u) [CommRing R]
    {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ)
    (hY : IsZero (SingularCohomology R (TopCat.of Y) n)) :
    IsZero (SingularCohomology R (TopCat.of X) n) := by
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  have H : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := by
    simpa [f, g, TopCat.Homotopy] using e.left_inv.some
  exact singularCohomology_isZero_of_left_homotopy_inverse R f g H n hY

/--
%%handwave
name:
  Homotopy equivalent spaces have the same vanishing singular cohomology
statement:
  If \(X\) and \(Y\) are homotopy equivalent, then \(H^n(X;R)=0\) if and only
  if \(H^n(Y;R)=0\).
proof:
  Apply the preceding vanishing-preservation statement to the homotopy
  equivalence and to its inverse.
-/
theorem singularCohomology_isZero_iff_of_homotopyEquiv
    (R : Type u) [CommRing R]
    {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    IsZero (SingularCohomology R (TopCat.of X) n) ↔
      IsZero (SingularCohomology R (TopCat.of Y) n) := by
  constructor
  · intro hX
    exact singularCohomology_isZero_of_homotopyEquiv R e.symm n hX
  · intro hY
    exact singularCohomology_isZero_of_homotopyEquiv R e n hY

/--
%%handwave
name:
  Dual cohomology vanishes when homology vanishes over the reals
statement:
  For a chain complex of real vector spaces, if homology in degree \(n\)
  vanishes, then the degree \(n\) cohomology of the dual cochain complex with
  coefficients in a real vector space vanishes.
proof:
  Over a field every short exact sequence of vector spaces splits, so taking
  linear maps into a fixed vector space is exact.  Therefore the cohomology of
  the dual complex is naturally the dual of homology.
-/
theorem linearYonedaObj_homology_isZero_of_homology_isZero
    (K : ChainComplex (ModuleCat.{v} ℝ) ℕ) (A : ModuleCat.{v} ℝ) (n : ℕ)
    (h : IsZero (K.homology n)) :
    IsZero ((K.linearYonedaObj ℝ A).homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology] at h ⊢
  have hKop : K.op.ExactAt n := h.op
  change ((K.linearYonedaObj ℝ A).sc n).Exact
  change ((K.op.sc n).map (((linearYoneda ℝ (ModuleCat.{v} ℝ)).obj A))).Exact
  rw [ShortComplex.exact_iff_exact_map_forget₂]
  haveI : Module.Injective ℝ A := Module.injective_of_isSemisimpleRing ℝ A
  haveI : CategoryTheory.Injective A := by
    change CategoryTheory.Injective (ModuleCat.of ℝ A)
    exact Module.injective_object_of_injective_module ℝ A
  have hpre : ((K.op.sc n).map (preadditiveYonedaObj A)).Exact := by
    exact hKop.map (preadditiveYonedaObj A)
  have hpre_forget :
      (((K.op.sc n).map (preadditiveYonedaObj A)).map
        (forget₂ (ModuleCat.{v} (End A)) Ab)).Exact := by
    exact hpre.map (forget₂ (ModuleCat.{v} (End A)) Ab)
  change
    (((K.op.sc n).map (preadditiveYonedaObj A)).map
      (forget₂ (ModuleCat.{v} (End A)) Ab)).Exact
  exact hpre_forget

/--
%%handwave
name:
  Totally disconnected spaces have no positive real singular cohomology
statement:
  If \(X\) is totally disconnected, then \(H^{m+1}(X;\mathbb R)=0\) for
  every \(m\ge 0\).
proof:
  Mathlib computes the positive singular homology of a totally disconnected
  space as zero.  Apply exactness of real linear duals to pass from homology
  to cohomology.
-/
theorem realSingularCohomology_positive_isZero_of_totallyDisconnected
    (X : TopCat.{v}) [TotallyDisconnectedSpace X] (m : ℕ) :
    IsZero (RealSingularCohomology X (m + 1)) := by
  exact
    linearYonedaObj_homology_isZero_of_homology_isZero
      (SingularChains ℝ X)
      (SingularCohomologyCoefficient.{0, v} ℝ) (m + 1)
      (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        (C := ModuleCat.{v} ℝ) (n := m + 1)
        (R := SingularCohomologyCoefficient.{0, v} ℝ) (X := X) (by omega))

/--
%%handwave
name:
  Vanishing first homology gives vanishing first cohomology over the reals
statement:
  If \(H_1(X;\mathbb R)=0\), then \(H^1(X;\mathbb R)=0\).
proof:
  Apply exactness of linear duals over the field \(\mathbb R\) to the singular
  chain complex.
-/
theorem realSingularCohomology_one_isZero_of_realSingularHomology_one_isZero
    (X : TopCat.{v})
    (hH1 : IsZero (RealSingularHomology X 1)) :
    IsZero (RealSingularCohomology X 1) := by
  exact
    linearYonedaObj_homology_isZero_of_homology_isZero
      (SingularChains ℝ X)
      (SingularCohomologyCoefficient.{0, v} ℝ) 1 hH1






end

end Cohomology
end JJMath
