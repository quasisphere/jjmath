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
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.Points
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Homotopy.LocallyContractible
import JJMath.Topology.SmallSingularChains
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
open TopCat
open TopCat.Presheaf
open TopologicalSpace
open HomologicalComplex
open scoped Topology
open scoped AlgebraicGeometry

namespace JJMath
namespace Cohomology

noncomputable section

universe u v wFlasque

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

/--
%%handwave
name:
  Evaluation of scalar multiplication on the lifted real line
statement:
  Multiplication by \(r\) sends a lifted real number \(x\) to the lift of
  \(r\,x\).
proof:
  This is the defining formula for the additive endomorphism.
-/
@[simp]
theorem realULiftScalarAddMonoidHom_apply (r : ℝ) (x : ULift.{v} ℝ) :
    realULiftScalarAddMonoidHom.{v} r x = ULift.up (r * x.down) :=
  rfl

/--
%%handwave
name:
  Multiplication by one on the lifted real line
statement:
  Scalar multiplication by \(1\) is the identity additive endomorphism of the
  lifted real line.
proof:
  Evaluate at a lifted real number and simplify \(1x=x\).
-/
@[simp]
theorem realULiftScalarAddMonoidHom_one :
    realULiftScalarAddMonoidHom.{v} (1 : ℝ) =
      AddMonoidHom.id (ULift.{v} ℝ) := by
  ext x
  cases x
  simp

/--
%%handwave
name:
  Composition of scalar multiplications on the lifted real line
statement:
  Multiplication by \(rs\) equals multiplication by \(s\), followed by
  multiplication by \(r\).
proof:
  Evaluate at \(x\) and use associativity \(r(sx)=(rs)x\).
-/
theorem realULiftScalarAddMonoidHom_mul (r s : ℝ) :
    realULiftScalarAddMonoidHom.{v} (r * s) =
      (realULiftScalarAddMonoidHom.{v} r).comp
        (realULiftScalarAddMonoidHom.{v} s) := by
  ext x
  cases x
  simp [mul_assoc]

/--
%%handwave
name:
  Multiplication by zero on the lifted real line
statement:
  Scalar multiplication by \(0\) is the zero additive endomorphism of the
  lifted real line.
proof:
  Evaluate at \(x\) and simplify \(0x=0\).
-/
@[simp]
theorem realULiftScalarAddMonoidHom_zero :
    realULiftScalarAddMonoidHom.{v} (0 : ℝ) =
      0 := by
  ext x
  cases x
  simp

/--
%%handwave
name:
  Additivity of scalar endomorphisms on the lifted real line
statement:
  Multiplication by \(r+s\) is the sum of multiplication by \(r\) and
  multiplication by \(s\).
proof:
  Evaluate at \(x\) and distribute: \((r+s)x=rx+sx\).
-/
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

/--
%%handwave
name:
  Multiplication by one on the constant real sheaf
statement:
  The scalar endomorphism of the constant real sheaf associated to \(1\) is
  the identity.
proof:
  The underlying coefficient endomorphism is the identity, and the
  constant-sheaf functor preserves identities.
-/
@[simp]
theorem realConstantSheafScalarEnd_one (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    realConstantSheafScalarEnd X (1 : ℝ) = 𝟙 (RealConstantAddSheaf X) := by
  simp [realConstantSheafScalarEnd]

/--
%%handwave
name:
  Multiplication by zero on the constant real sheaf
statement:
  The scalar endomorphism of the constant real sheaf associated to \(0\) is
  the zero morphism.
proof:
  The coefficient endomorphism is zero, and the additive constant-sheaf
  functor preserves zero morphisms.
-/
@[simp]
theorem realConstantSheafScalarEnd_zero (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    realConstantSheafScalarEnd X (0 : ℝ) = 0 := by
  rw [realConstantSheafScalarEnd, realULiftScalarAddMonoidHom_zero]
  exact Functor.map_zero _ _ _

/--
%%handwave
name:
  Additivity of scalar endomorphisms of the constant real sheaf
statement:
  On the constant real sheaf, multiplication by \(r+s\) is the sum of
  multiplication by \(r\) and multiplication by \(s\).
proof:
  Coefficient multiplication is additive in the scalar, and the
  constant-sheaf functor preserves addition of morphisms.
-/
theorem realConstantSheafScalarEnd_add (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (r s : ℝ) :
    realConstantSheafScalarEnd X (r + s) =
      realConstantSheafScalarEnd X r + realConstantSheafScalarEnd X s := by
  rw [realConstantSheafScalarEnd, realULiftScalarAddMonoidHom_add]
  exact Functor.map_add _

/--
%%handwave
name:
  Composition of scalar endomorphisms of the constant real sheaf
statement:
  On the constant real sheaf, multiplication by \(rs\) is multiplication by
  \(s\), followed by multiplication by \(r\).
proof:
  Apply functoriality of the constant-sheaf construction to the corresponding
  composition identity on the coefficient group.
-/
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

/--
%%handwave
name:
  Successor for the reversed complex shape
statement:
  For every complex shape \(c\) and degree \(i\), the successor of \(i\) in
  the reversed shape is the predecessor of \(i\) in \(c\).
proof:
  If an incoming relation exists, both sides are its source.  Otherwise both
  operations fix \(i\).
-/
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

/--
%%handwave
name:
  Predecessor for the reversed complex shape
statement:
  For every complex shape \(c\) and degree \(i\), the predecessor of \(i\) in
  the reversed shape is the successor of \(i\) in \(c\).
proof:
  Apply the corresponding successor identity to the reversed shape and use
  that reversing twice returns the original shape.
-/
private lemma complexShape_symm_prev_eq_next_for_singularCohomology
    {ι : Type*} (c : ComplexShape ι) (i : ι) :
    c.symm.prev i = c.next i := by
  simpa using (complexShape_symm_next_eq_prev_for_singularCohomology c.symm i).symm

/--
%%handwave
name:
  A homotopy survives passage out of an opposite category
statement:
  If two maps of complexes in an opposite preadditive category are homotopic,
  then the maps obtained by taking opposites and passing to the corresponding
  complexes in the original category are homotopic.
proof:
  Reverse the two degree indices of every homotopy component and take its
  opposite.  Taking opposites reverses composition, while the successor and
  predecessor of the reversed complex shape interchange, yielding the
  required homotopy identity.
-/
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

/--
%%handwave
name:
  Chain homotopies induce cochain homotopies
statement:
  A homotopy between the singular-chain maps induced by \(f,g:X\to Y\)
  gives a homotopy between the pullback maps
  \(C^\bullet(Y;R)\to C^\bullet(X;R)\).
proof:
  Apply the contravariant linear-dual functor to the chain homotopy, then pass
  from complexes in the opposite module category to cochain complexes in the
  module category.
-/
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
  Augmentation from constants to singular zero-cochains
statement:
  On each open subset of a space $X$, a real constant determines the singular $0$-cochain taking that value on every singular $0$-simplex; these maps form a natural transformation of presheaves.
-/
noncomputable def realConstantOpenPresheafToSingularCochainZeroPresheaf
    (X : TopCat.{v}) :
    realConstantOpenPresheaf X ⟶
      (realSingularCochainOpenPresheafComplex X).X 0 :=
  standardRealConstantOpenPresheafToSingularCochainZeroPresheaf X

/--
%%handwave
name:
  Full specification of the constant singular zero-cochain augmentation
statement:
  The standard natural map
  \(\eta:\underline{\mathbb R}\to C^0(-;\mathbb R)\) has four properties:
  \(d\eta=0\); it commutes with multiplication by every \(r\in\mathbb R\);
  after restriction along a null-homotopic inclusion \(V\subseteq U\), every
  closed zero-cochain on \(U\) is in the image of \(\eta_V\); and a constant
  section whose image has zero germ already has zero germ.
proof:
  Combine the previously proved closedness, scalar compatibility, local
  constancy under null-homotopic restriction, and germ-detection properties
  of the standard augmentation.
-/
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

/--
%%handwave
name:
  Closedness and scalar compatibility of the constant augmentation
statement:
  The standard map
  \(\eta:\underline{\mathbb R}\to C^0(-;\mathbb R)\) satisfies
  \(d\eta=0\) and \(M_r\eta=\eta S_r\) for every real scalar \(r\).
proof:
  Extract these first two conclusions from the full specification of the
  standard augmentation.
-/
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

/--
%%handwave
name:
  Unit scalar on real constant-sheaf cohomology
statement:
  For every cohomology class \(\alpha\), one has \(1\cdot\alpha=\alpha\).
proof:
  Multiplication by \(1\) is the identity coefficient morphism, and composing
  an Ext class with the identity leaves it unchanged.
-/
@[simp]
theorem realConstantSheafCohomologySMul_one (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) (α : RealConstantSheafCohomology X n) :
    realConstantSheafCohomologySMul X n (1 : ℝ) α = α := by
  simp [realConstantSheafCohomologySMul]

/--
%%handwave
name:
  Zero scalar on real constant-sheaf cohomology
statement:
  For every cohomology class \(\alpha\), one has \(0\cdot\alpha=0\).
proof:
  Multiplication by \(0\) is the zero coefficient morphism, so postcomposition
  of the Ext class is zero.
-/
@[simp]
theorem realConstantSheafCohomologySMul_zero_scalar (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) (α : RealConstantSheafCohomology X n) :
    realConstantSheafCohomologySMul X n (0 : ℝ) α = 0 := by
  simp [realConstantSheafCohomologySMul, realConstantSheafScalarEnd_zero]

/--
%%handwave
name:
  Scalar multiplication preserves the zero cohomology class
statement:
  For every real \(r\), one has \(r\cdot0=0\) in real constant-sheaf
  cohomology.
proof:
  The zero Ext class remains zero after composition with any coefficient
  endomorphism.
-/
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

/--
%%handwave
name:
  Distributivity over addition of cohomology classes
statement:
  For \(r\in\mathbb R\) and cohomology classes \(\alpha,\beta\),
  \(r\cdot(\alpha+\beta)=r\cdot\alpha+r\cdot\beta\).
proof:
  Composition in Ext is additive in its first argument.
-/
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

/--
%%handwave
name:
  Distributivity over addition of scalars
statement:
  For \(r,s\in\mathbb R\) and a cohomology class \(\alpha\),
  \((r+s)\cdot\alpha=r\cdot\alpha+s\cdot\alpha\).
proof:
  The coefficient endomorphism for \(r+s\) is the sum of those for \(r\) and
  \(s\), and composition in Ext is additive in the second argument.
-/
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

/--
%%handwave
name:
  Associativity of scalar multiplication on constant-sheaf cohomology
statement:
  For \(r,s\in\mathbb R\) and a cohomology class \(\alpha\),
  \((rs)\cdot\alpha=r\cdot(s\cdot\alpha)\).
proof:
  Multiplication by \(rs\) is the composite of the coefficient endomorphisms
  for \(s\) and \(r\); associativity of Ext composition gives the result.
-/
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

/--
%%handwave
name:
  Homotopic maps induce the same singular-cohomology pullback
statement:
  If \(f,g:X\to Y\) are homotopic, then their induced maps
  \(H^n(Y;R)\to H^n(X;R)\) are equal for every \(n\).
proof:
  The homotopy induces a chain homotopy on singular chains.  Dualizing gives
  a cochain homotopy between the pullback maps, and homotopic cochain maps
  induce the same map on cohomology.
-/
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

/--
%%handwave
name:
  The dual of a degree-zero complex has no positive cohomology
statement:
  Let \(A\) be an \(R\)-module and regard it as a chain complex concentrated
  in degree \(0\).  Its linear-dual cochain complex has zero cohomology in
  every degree \(m+1\).
proof:
  After taking opposites, the dual complex is still concentrated in degree
  zero, so it is exact in every positive degree.
-/
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

/--
%%handwave
name:
  The dual alternating constant complex has no positive cohomology
statement:
  For an \(R\)-module \(A\), the linear dual of the alternating constant chain
  complex on \(A\) has zero cohomology in every degree \(m+1\).
proof:
  The alternating constant complex is chain-homotopy equivalent to the
  complex concentrated in degree zero.  Linear duality preserves this
  homotopy equivalence, and the latter dual complex has no positive
  cohomology.
-/
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

/--
%%handwave
name:
  A constant map induces zero in positive singular cohomology
statement:
  For \(m\ge0\), the pullback in degree \(m+1\) induced by a constant map
  \(V\to U\) is the zero map.
proof:
  Factor the constant map through a point.  Contravariance factors its
  cohomology pullback through the positive-degree cohomology of a point,
  which is zero.
-/
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
  Locally finite shrinking of an open cover inside a paracompact open subspace
statement:
  Let $U$ be a paracompact open subspace of a Hausdorff space and let
  $(O_i)$ be an open cover of $U$.  There is an open cover $(W_i)$ of $U$
  with $W_i\subseteq O_i$ such that the induced family on $U$ is locally
  finite and the closure of $W_i$ in $U$ is contained in $O_i$.
proof:
  First take a precise locally finite refinement on the paracompact subspace
  $U$.  Since a paracompact Hausdorff space is normal, apply the shrinking
  lemma to that refinement and transport the resulting open subsets of $U$
  back to open subsets of the ambient space.
-/
theorem exists_locallyFinite_open_shrinking
    (X : TopCat.{v}) [T2Space X]
    (U : Opens X) [ParacompactSpace U]
    {κ : Type v} (O : κ → Opens X)
    (hcover : ∀ x : X, x ∈ U → ∃ i, x ∈ O i) :
    ∃ W : κ → Opens X,
      (∀ i, W i ≤ O i) ∧
      (∀ x : X, x ∈ U → ∃ i, x ∈ W i) ∧
      LocallyFinite
        (fun i => (Subtype.val : U → X) ⁻¹' (W i : Set X)) ∧
      ∀ i, closure ((Subtype.val : U → X) ⁻¹' (W i : Set X)) ⊆
        (Subtype.val : U → X) ⁻¹' (O i : Set X) := by
  classical
  let Osub : κ → Set U :=
    fun i => (Subtype.val : U → X) ⁻¹' (O i : Set X)
  have hOsubOpen : ∀ i, IsOpen (Osub i) := by
    intro i
    exact (O i).isOpen.preimage continuous_subtype_val
  have hOsubCover : ⋃ i, Osub i = (Set.univ : Set U) := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    rcases hcover x.1 x.2 with ⟨i, hxi⟩
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩
  rcases precise_refinement Osub hOsubOpen hOsubCover with
    ⟨Q, hQopen, hQcover, hQfinite, hQO⟩
  letI : T4Space U := T4Space.of_paracompactSpace_t2Space
  rcases
      exists_iUnion_eq_closure_subset
        hQopen hQfinite.point_finite hQcover with
    ⟨V, hVcover, hVopen, hVclosure⟩
  let W : κ → Opens X := fun i =>
    ⟨Subtype.val '' V i,
      (U.isOpenEmbedding'.isOpen_iff_image_isOpen).mp (hVopen i)⟩
  have hVQ : ∀ i, V i ⊆ Q i := by
    intro i
    exact Set.Subset.trans subset_closure (hVclosure i)
  have hpreimageW : ∀ i,
      (Subtype.val : U → X) ⁻¹' (W i : Set X) = V i := by
    intro i
    apply Set.ext
    intro x
    simp only [W, SetLike.mem_coe, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyeq : y = x := Subtype.ext hyx
      simpa [hyeq] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · intro i x hx
    rcases hx with ⟨y, hyV, rfl⟩
    exact hQO i (hVQ i hyV)
  · intro x hxU
    have hxsub : (⟨x, hxU⟩ : U) ∈ ⋃ i, V i := by
      rw [hVcover]
      trivial
    rcases Set.mem_iUnion.mp hxsub with ⟨i, hxi⟩
    exact ⟨i, ⟨⟨x, hxU⟩, hxi, rfl⟩⟩
  · simpa only [hpreimageW] using hQfinite.subset hVQ
  · intro i
    rw [hpreimageW i]
    exact (hVclosure i).trans (hQO i)

/--
%%handwave
name:
  The target open set of a singular simplex is nonempty
statement:
  If there is a singular $p$-simplex with image in an open set $U$, then
  $U$ is nonempty.
proof:
  The standard $p$-simplex is nonempty.  Evaluate the singular simplex at any
  one of its points to obtain a point of $U$.
-/
theorem openSingularSimplex_target_nonempty
    (X : TopCat.{v}) (p : ℕ) (U : Opens X)
    (σ : openSingularSimplex X p U) :
    (U : Set X).Nonempty := by
  let c :=
    TopCat.toSSetObjEquiv ((Opens.toTopCat X).obj U)
      (op (SimplexCategory.mk p)) σ
  let z : stdSimplex ℝ (Fin (p + 1)) := Classical.choice inferInstance
  exact ⟨(c z).1, (c z).2⟩











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
  Locally chosen singular cochains determine a global cochain
statement:
  Given singular cochains on open subsets of an open set $U$, there is a
  singular cochain on $U$ whose value on each simplex lying in one of those
  subsets is the value of one chosen local representative of that simplex.
proof:
  Choose one local representative of each representable simplex and use its
  prescribed value.  Assign zero to the other simplices and extend the
  assignment linearly from the free real vector space on singular simplices.
-/
theorem realSingularCochainOpenPresheafComplex_exists_global_cochain_of_chosen_local_simplex
    (X : TopCat.{v}) (p : ℕ) (U : Opens X)
    {κ : Type v}
    (W : κ → Opens X)
    (hWU : ∀ a : κ, W a ≤ U)
    (τ : ∀ a : κ,
      ((realSingularCochainOpenPresheafComplex X).X p).obj (op (W a))) :
    ∃ T : ((realSingularCochainOpenPresheafComplex X).X p).obj (op U),
      ∀ σU : openSingularSimplex X p U,
        (∃ (a : κ) (σa : openSingularSimplex X p (W a)),
          openSingularSimplexMap X p (hWU a) σa = σU) →
        ∃ (a : κ) (σa : openSingularSimplex X p (W a)),
          openSingularSimplexMap X p (hWU a) σa = σU ∧
            openSingularCochainSimplexEval X p U T σU =
              openSingularCochainSimplexEval X p (W a) (τ a) σa := by
  classical
  let Simplex (O : Opens X) := openSingularSimplex X p O
  let EndCoeff :=
    SingularCohomologyCoefficient.{0, v} ℝ ⟶
      SingularCohomologyCoefficient.{0, v} ℝ
  let mapToU (a : κ) : Simplex (W a) → Simplex U :=
    openSingularSimplexMap X p (hWU a)
  let Rep (σ : Simplex U) : Type v :=
    Σ a : κ, {σa : Simplex (W a) // mapToU a σa = σ}
  let evalRep : ∀ {σ : Simplex U}, Rep σ → EndCoeff :=
    fun {_} r =>
      openSingularCochainSimplexEval X p (W r.1) (τ r.1) r.2.1
  let φ : ∀ σ : Simplex U, EndCoeff :=
    fun σ =>
      if h : Nonempty (Rep σ) then evalRep (Classical.choice h) else 0
  let T : (SingularCochainComplex ℝ ((Opens.toTopCat X).obj U)).X p :=
    singularCochainOfSimplexEnd ((Opens.toTopCat X).obj U) p φ
  refine ⟨T, ?_⟩
  intro σU hσU
  have hrep : Nonempty (Rep σU) := by
    rcases hσU with ⟨a, σa, hσa⟩
    exact ⟨⟨a, ⟨σa, by simpa [mapToU] using hσa⟩⟩⟩
  let r : Rep σU := Classical.choice hrep
  refine ⟨r.1, r.2.1, ?_, ?_⟩
  · simpa [mapToU] using r.2.2
  · have heval :=
      singularCochainOfSimplexEnd_eval
        ((Opens.toTopCat X).obj U) p φ σU
    calc
      openSingularCochainSimplexEval X p U T σU = φ σU := by
        simpa [T, openSingularCochainSimplexEval] using heval
      _ = evalRep r := by
        simp only [φ, dif_pos hrep]
        rfl
      _ =
          openSingularCochainSimplexEval X p (W r.1) (τ r.1) r.2.1 := by
        rfl

/--
%%handwave
name:
  Singular cochains represent sheafified sections on paracompact open sets
statement:
  Let $U$ be a paracompact open subspace of a Hausdorff space.  Every section
  over $U$ of the sheafification of degree-$p$ real singular cochains is
  represented by an ordinary singular cochain on $U$.
proof:
  Choose local cochain representatives and shrink their cover to a locally
  finite cover whose closures remain inside the representing domains.  Define
  a global cochain by choosing one local value for every singular simplex.
  Near a fixed point, only finitely many shrunk domains can occur, and every
  one which still occurs has closure through that point.  Local injectivity
  of sheafification therefore supplies one neighborhood on which all possible
  chosen values agree.  Hence the global cochain sheafifies to the original
  section locally, and separatedness of the sheaf gives equality on $U$.
-/
theorem realSingularCochain_toSheafify_app_surjective_of_paracompact
    (X : TopCat.{v}) [T2Space X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (p : ℕ) (U : Opens X) [ParacompactSpace U] :
    Function.Surjective
      (ConcreteCategory.hom
        ((CategoryTheory.toSheafify
          (Opens.grothendieckTopology X)
          ((realSingularCochainOpenPresheafComplex X).X p)).app (op U))) := by
  classical
  let P : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X p
  intro s
  have hlocal := fun x : U =>
    addCommGrp_toSheafify_locally_represented
      (X := X) P s x.1 x.2
  choose O hOU hxO t ht using hlocal
  have hcover : ∀ x : X, x ∈ U → ∃ i : U, x ∈ O i := by
    intro x hx
    exact ⟨⟨x, hx⟩, hxO ⟨x, hx⟩⟩
  rcases exists_locallyFinite_open_shrinking X U O hcover with
    ⟨W, hWO, hWcover, hWfinite, hWclosure⟩
  have hWU : ∀ i, W i ≤ U := fun i => (hWO i).trans (hOU i)
  let τ : ∀ i, P.obj (op (W i)) := fun i =>
    P.map (homOfLE (hWO i)).op (t i)
  have hτ : ∀ i,
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X) P).app (op (W i))) (τ i) =
        (CategoryTheory.sheafify
          (Opens.grothendieckTopology X) P).map
            (homOfLE (hWU i)).op s := by
    intro i
    have hnat :=
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology X) P).naturality
          (homOfLE (hWO i)).op
    have happ := congrArg (fun f => (ConcreteCategory.hom f) (t i)) hnat
    calc
      ((CategoryTheory.toSheafify
          (Opens.grothendieckTopology X) P).app (op (W i))) (τ i) =
        (CategoryTheory.sheafify
          (Opens.grothendieckTopology X) P).map (homOfLE (hWO i)).op
            (((CategoryTheory.toSheafify
              (Opens.grothendieckTopology X) P).app (op (O i))) (t i)) := by
          simpa [τ, ConcreteCategory.comp_apply] using happ.symm
      _ =
        (CategoryTheory.sheafify
          (Opens.grothendieckTopology X) P).map (homOfLE (hWO i)).op
            ((CategoryTheory.sheafify
              (Opens.grothendieckTopology X) P).map
                (homOfLE (hOU i)).op s) := by
          rw [ht i]
      _ =
        (CategoryTheory.sheafify
          (Opens.grothendieckTopology X) P).map
            (homOfLE (hWU i)).op s := by
          rw [← ConcreteCategory.comp_apply, ←
            (CategoryTheory.sheafify
              (Opens.grothendieckTopology X) P).map_comp]
          congr 2
  rcases
      realSingularCochainOpenPresheafComplex_exists_global_cochain_of_chosen_local_simplex
        (X := X) (p := p) (U := U) W hWU τ with
    ⟨T, hT⟩
  refine ⟨T, ?_⟩
  apply
    realSingularCochainOpenPresheafComplex_sheafified_section_eq_of_locally_eq
      (X := X) (p := p)
  intro x hxU
  let xU : U := ⟨x, hxU⟩
  rcases hWcover x hxU with ⟨i₀, hxi₀⟩
  have hxi₀O : x ∈ O i₀ := hWO i₀ hxi₀
  rcases hWfinite xU with ⟨A, hA_nhds, hAfinite⟩
  rcases mem_nhds_iff.mp hA_nhds with ⟨B, hBA, hBopen, hxB⟩
  let S : Set U :=
    {j | ((Subtype.val : U → X) ⁻¹' (W j : Set X) ∩ A).Nonempty}
  have hSfinite : S.Finite := by
    simpa [S] using hAfinite
  have hCexists : ∀ j : U,
      ∃ C : Opens X, x ∈ C ∧ C ≤ U ∧
        ((C ⊓ W j = ⊥) ∨
          ∃ (hCi₀ : C ≤ O i₀) (hCj : C ≤ O j),
            P.map (homOfLE hCi₀).op (t i₀) =
              P.map (homOfLE hCj).op (t j)) := by
    intro j
    by_cases hxj :
        xU ∈ closure ((Subtype.val : U → X) ⁻¹' (W j : Set X))
    · have hxjO : x ∈ O j := hWclosure j hxj
      rcases
          realSingularCochainOpenPresheafComplex_openCover_localCompatibility_of_represent_same_sheafified_section
            (X := X) (p := p) (U := U) O hOU s t ht
            i₀ j x hxi₀O hxjO with
        ⟨C, hCi₀, hCj, hxC, hEq⟩
      exact
        ⟨C, hxC, hCi₀.trans (hOU i₀), Or.inr
          ⟨hCi₀, hCj, hEq⟩⟩
    · let D : Set U :=
        (closure
          ((Subtype.val : U → X) ⁻¹' (W j : Set X)))ᶜ
      have hDopen : IsOpen D := isClosed_closure.isOpen_compl
      let Cj : Opens X :=
        ⟨Subtype.val '' D,
          (U.isOpenEmbedding'.isOpen_iff_image_isOpen).mp hDopen⟩
      have hxD : xU ∈ D := hxj
      refine ⟨Cj, ⟨xU, hxD, rfl⟩, ?_, Or.inl ?_⟩
      · intro y hy
        rcases hy with ⟨z, _hzD, rfl⟩
        exact z.2
      · apply le_antisymm
        · intro y hy
          rcases hy.1 with ⟨z, hzD, hzy⟩
          have hzW :
              z ∈ (Subtype.val : U → X) ⁻¹' (W j : Set X) := by
            change z.1 ∈ W j
            rw [hzy]
            exact hy.2
          exact (hzD (subset_closure hzW)).elim
        · exact bot_le
  choose C hxC hCU hCcase using hCexists
  let sA : Finset U := hSfinite.toFinset
  let Bopen : Opens X :=
    ⟨Subtype.val '' B,
      (U.isOpenEmbedding'.isOpen_iff_image_isOpen).mp hBopen⟩
  let N : Opens X :=
    ⟨(Bopen : Set X) ∩ (W i₀ : Set X) ∩
        ⋂ j ∈ sA, (C j : Set X),
      ((Bopen.isOpen.inter (W i₀).isOpen).inter
        (isOpen_biInter_finset fun j _hj => (C j).isOpen))⟩
  have hxBopen : x ∈ Bopen := ⟨xU, hxB, rfl⟩
  have hxN : x ∈ N := by
    refine ⟨⟨hxBopen, hxi₀⟩, ?_⟩
    exact Set.mem_iInter₂.mpr fun j _hj => hxC j
  have hNB : N ≤ Bopen := fun _ hy => hy.1.1
  have hNWi₀ : N ≤ W i₀ := fun _ hy => hy.1.2
  have hNU : N ≤ U := hNWi₀.trans (hWU i₀)
  have hNC : ∀ j, j ∈ sA → N ≤ C j := by
    intro j hj _ hy
    exact Set.mem_iInter₂.mp hy.2 j hj
  have hactive : ∀ j, ((N ⊓ W j : Opens X) : Set X).Nonempty → j ∈ sA := by
    intro j hj
    rcases hj with ⟨y, hyN, hyWj⟩
    rcases hNB hyN with ⟨z, hzB, hzy⟩
    have hzWj :
        z ∈ (Subtype.val : U → X) ⁻¹' (W j : Set X) := by
      change z.1 ∈ W j
      rw [hzy]
      exact hyWj
    have hjS : j ∈ S := by
      exact ⟨z, hzWj, hBA hzB⟩
    simpa [sA] using hjS
  have hpairAt : ∀ j,
      ((N ⊓ W j : Opens X) : Set X).Nonempty →
        ∃ (hAi₀ : N ⊓ W j ≤ O i₀) (hAj : N ⊓ W j ≤ O j),
          P.map (homOfLE hAi₀).op (t i₀) =
            P.map (homOfLE hAj).op (t j) := by
    intro j hjnonempty
    have hjsA := hactive j hjnonempty
    have hNjC : N ≤ C j := hNC j hjsA
    rcases hCcase j with hdisjoint | ⟨hCi₀, hCj, hEq⟩
    · rcases hjnonempty with ⟨y, hyN, hyWj⟩
      have hybot : y ∈ (⊥ : Opens X) := by
        rw [← hdisjoint]
        exact ⟨hNjC hyN, hyWj⟩
      exact hybot.elim
    · let Aopen : Opens X := N ⊓ W j
      have hAC : Aopen ≤ C j := fun _ hy => hNjC hy.1
      have hAi₀ : Aopen ≤ O i₀ := hAC.trans hCi₀
      have hAj : Aopen ≤ O j := hAC.trans hCj
      refine ⟨hAi₀, hAj, ?_⟩
      have hEq' :=
        congrArg (fun q => P.map (homOfLE hAC).op q) hEq
      simpa only [← ConcreteCategory.comp_apply, ← P.map_comp] using hEq'
  have hTN :
      P.map (homOfLE hNU).op T =
        P.map
          (homOfLE (hNWi₀.trans (hWO i₀))).op (t i₀) := by
    apply
      realSingularCochainOpenPresheafComplex_eq_of_forall_simplex_eval_eq
        (X := X) (p := p) (U := N)
    intro σN
    let σU : openSingularSimplex X p U :=
      openSingularSimplexMap X p hNU σN
    let σi₀ : openSingularSimplex X p (W i₀) :=
      openSingularSimplexMap X p hNWi₀ σN
    have hσi₀ :
        openSingularSimplexMap X p (hWU i₀) σi₀ = σU := by
      apply
        (TopCat.toSSetObjEquiv ((Opens.toTopCat X).obj U)
          (op (SimplexCategory.mk p))).injective
      simp only [σi₀, σU, toSSetObjEquiv_map_apply]
      rfl
    rcases hT σU ⟨i₀, σi₀, hσi₀⟩ with
      ⟨j, σj, hσj, hEval⟩
    have hσNU :
        openSingularSimplexMap X p hNU σN =
          openSingularSimplexMap X p (hWU j) σj := by
      exact hσj.symm
    rcases
        openSingularSimplex_exists_lift_inf_of_map_eq
          (X := X) (p := p) (U := U) (A := N) (B := W j)
          hNU (hWU j) σN σj hσNU with
      ⟨σA, hσAN, hσAW⟩
    have hAne : (((N ⊓ W j : Opens X) : Set X)).Nonempty :=
      openSingularSimplex_target_nonempty X p (N ⊓ W j) σA
    rcases hpairAt j hAne with ⟨hAi₀, hAj, hpair⟩
    have hleft :
        openSingularCochainSimplexEval X p N
            (P.map (homOfLE hNU).op T) σN =
          openSingularCochainSimplexEval X p U T σU := by
      simpa [P, σU] using
        (openSingularCochainSimplexEval_restrict
          (X := X) (p := p) hNU T σN)
    have hτeval :
        openSingularCochainSimplexEval X p (W j) (τ j) σj =
          openSingularCochainSimplexEval X p (O j) (t j)
            (openSingularSimplexMap X p (hWO j) σj) := by
      simpa [P, τ] using
        (openSingularCochainSimplexEval_restrict
          (X := X) (p := p) (hWO j) (t j) σj)
    have hpairEvalA :
        openSingularCochainSimplexEval X p (O i₀) (t i₀)
            (openSingularSimplexMap X p hAi₀ σA) =
          openSingularCochainSimplexEval X p (O j) (t j)
            (openSingularSimplexMap X p hAj σA) := by
      have hp :=
        congrArg
          (fun q =>
            openSingularCochainSimplexEval X p (N ⊓ W j) q σA)
          hpair
      have hleftA :=
        openSingularCochainSimplexEval_restrict
          (X := X) (p := p) hAi₀ (t i₀) σA
      have hrightA :=
        openSingularCochainSimplexEval_restrict
          (X := X) (p := p) hAj (t j) σA
      exact hleftA.symm.trans (hp.trans hrightA)
    have hmap_i₀ :
        openSingularSimplexMap X p hAi₀ σA =
          openSingularSimplexMap X p
            (hNWi₀.trans (hWO i₀)) σN := by
      calc
        openSingularSimplexMap X p hAi₀ σA =
            openSingularSimplexMap X p
              (hNWi₀.trans (hWO i₀))
              (openSingularSimplexMap X p inf_le_left σA) := by
          apply
            (TopCat.toSSetObjEquiv ((Opens.toTopCat X).obj (O i₀))
              (op (SimplexCategory.mk p))).injective
          simp only [toSSetObjEquiv_map_apply]
          rfl
        _ =
            openSingularSimplexMap X p
              (hNWi₀.trans (hWO i₀)) σN := by
          rw [hσAN]
    have hmap_j :
        openSingularSimplexMap X p hAj σA =
          openSingularSimplexMap X p (hWO j) σj := by
      calc
        openSingularSimplexMap X p hAj σA =
            openSingularSimplexMap X p (hWO j)
              (openSingularSimplexMap X p inf_le_right σA) := by
          apply
            (TopCat.toSSetObjEquiv ((Opens.toTopCat X).obj (O j))
              (op (SimplexCategory.mk p))).injective
          simp only [toSSetObjEquiv_map_apply]
          rfl
        _ = openSingularSimplexMap X p (hWO j) σj := by
          rw [hσAW]
    have hright :
        openSingularCochainSimplexEval X p N
            (P.map
              (homOfLE (hNWi₀.trans (hWO i₀))).op (t i₀)) σN =
          openSingularCochainSimplexEval X p (O i₀) (t i₀)
            (openSingularSimplexMap X p
              (hNWi₀.trans (hWO i₀)) σN) := by
      simpa [P] using
        (openSingularCochainSimplexEval_restrict
          (X := X) (p := p) (hNWi₀.trans (hWO i₀)) (t i₀) σN)
    calc
      openSingularCochainSimplexEval X p N
          (P.map (homOfLE hNU).op T) σN =
        openSingularCochainSimplexEval X p U T σU := hleft
      _ =
        openSingularCochainSimplexEval X p (W j) (τ j) σj := hEval
      _ =
        openSingularCochainSimplexEval X p (O j) (t j)
          (openSingularSimplexMap X p (hWO j) σj) := hτeval
      _ =
        openSingularCochainSimplexEval X p (O i₀) (t i₀)
          (openSingularSimplexMap X p
            (hNWi₀.trans (hWO i₀)) σN) := by
          rw [← hmap_j, ← hmap_i₀]
          exact hpairEvalA.symm
      _ =
        openSingularCochainSimplexEval X p N
          (P.map
            (homOfLE (hNWi₀.trans (hWO i₀))).op (t i₀)) σN :=
          hright.symm
  refine ⟨N, hNU, hxN, ?_⟩
  let J := Opens.grothendieckTopology X
  let F := CategoryTheory.sheafify J P
  let η : P ⟶ F := CategoryTheory.toSheafify J P
  have hnatU := η.naturality (homOfLE hNU).op
  have happU := congrArg (fun f => (ConcreteCategory.hom f) T) hnatU
  have hNOi₀ : N ≤ O i₀ := hNWi₀.trans (hWO i₀)
  have hnatO := η.naturality (homOfLE hNOi₀).op
  have happO := congrArg (fun f => (ConcreteCategory.hom f) (t i₀)) hnatO
  calc
    F.map (homOfLE hNU).op (η.app (op U) T) =
        η.app (op N) (P.map (homOfLE hNU).op T) := by
      simpa [ConcreteCategory.comp_apply] using happU
    _ =
        η.app (op N) (P.map (homOfLE hNOi₀).op (t i₀)) := by
      rw [hTN]
    _ =
        F.map (homOfLE hNOi₀).op (η.app (op (O i₀)) (t i₀)) := by
      simpa [ConcreteCategory.comp_apply] using happO.symm
    _ =
        F.map (homOfLE hNOi₀).op
          (F.map (homOfLE (hOU i₀)).op s) := by
      rw [ht i₀]
    _ = F.map (homOfLE hNU).op s := by
      rw [← ConcreteCategory.comp_apply, ← F.map_comp]
      congr 2

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
  The singular-cochain sheafification map is onto on paracompact open sets
statement:
  If $U$ is a paracompact open subspace of a Hausdorff space, then the map
  from ordinary real singular $p$-cochains on $U$ to sections over $U$ of
  their sheafification is an epimorphism.
proof:
  The underlying homomorphism is surjective by the direct locally finite
  section-lifting construction, and epimorphisms of abelian groups are exactly
  the surjective homomorphisms.
-/
theorem realSingularCochain_toSheafify_app_epi_of_paracompact
    (X : TopCat.{v}) [T2Space X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (p : ℕ) (U : Opens X) [ParacompactSpace U] :
    Epi ((CategoryTheory.toSheafify
      (Opens.grothendieckTopology X)
      ((realSingularCochainOpenPresheafComplex X).X p)).app (op U)) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  exact
    realSingularCochain_toSheafify_app_surjective_of_paracompact
      (X := X) p U

/--
%%handwave
name:
  The singular-cochain sheafification map is onto when all opens are paracompact
statement:
  On a Hausdorff space whose open subspaces are paracompact, the
  sheafification map from ordinary real singular $p$-cochains is an
  epimorphism on every open set.
proof:
  Install the assumed paracompactness instance for the requested open
  subspace and apply the paracompact-open section-lifting theorem.
-/
theorem realSingularCochain_toSheafify_app_epi_of_open_paracompact
    (X : TopCat.{v}) [T2Space X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (hopen : ∀ V : Opens X, ParacompactSpace V)
    (p : ℕ) (U : (Opens X)ᵒᵖ) :
    Epi ((CategoryTheory.toSheafify
      (Opens.grothendieckTopology X)
      ((realSingularCochainOpenPresheafComplex X).X p)).app U) := by
  letI : ParacompactSpace U.unop := hopen U.unop
  simpa using
    (realSingularCochain_toSheafify_app_epi_of_paracompact
      (X := X) p U.unop)

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

/--
%%handwave
name:
  Sheafified singular cochains are flasque when open subspaces are paracompact
statement:
  On a Hausdorff space whose open subspaces are paracompact, every degree of
  the sheafified real singular-cochain complex is a flasque sheaf.
proof:
  Ordinary singular cochains have surjective restriction maps.  The direct
  paracompact section-lifting theorem makes every component of the
  sheafification unit surjective, so extending a representative before
  sheafification proves surjectivity of every restriction map after
  sheafification.
-/
theorem realSingularCochainSheafComplex_isFlasque_of_open_paracompact
    (X : TopCat.{v}) [T2Space X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (hopen : ∀ V : Opens X, ParacompactSpace V)
    (p : ℕ) :
    TopCat.Sheaf.IsFlasque ((realSingularCochainSheafComplex X).X p) := by
  let P : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (realSingularCochainOpenPresheafComplex X).X p
  have hP : TopCat.Presheaf.IsFlasque P := by
    refine { epi := ?_ }
    intro U V i
    exact realSingularCochainOpenPresheafComplex_restriction_epi X p i
  have hunit :
      ∀ U : (Opens X)ᵒᵖ,
        Epi ((CategoryTheory.toSheafify
          (Opens.grothendieckTopology X) P).app U) := by
    intro U
    exact
      realSingularCochain_toSheafify_app_epi_of_open_paracompact
        (X := X) hopen p U
  simpa [P, realSingularCochainSheafComplex] using
    (sheafification_preserves_flasque_addCommGrp_of_toSheafify_app_epi
      (X := X) P hP hunit)




private noncomputable abbrev sheafSectionGenerator
    (X : TopCat.{v}) (U : Opens X)
    [HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}] :
    Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v} :=
  (presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}).obj
    (uliftYoneda.{max wFlasque v}.obj U ⋙ AddCommGrpCat.free)

private noncomputable def sheafSectionGeneratorMap
    (X : TopCat.{v}) {U V : Opens X}
    [HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    (f : U ⟶ V) :
    sheafSectionGenerator X U ⟶ sheafSectionGenerator X V :=
  (presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}).map
    (Functor.whiskerRight
      (uliftYoneda.{max wFlasque v}.map f) AddCommGrpCat.free)

private noncomputable def sheafSectionGeneratorHomEquiv
    (X : TopCat.{v}) (U : Opens X)
    [HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    (F : Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}) :
    (sheafSectionGenerator X U ⟶ F) ≃ F.obj.obj (op U) := by
  let J := Opens.grothendieckTopology X
  let e₁ : (sheafSectionGenerator X U ⟶ F) ≃
      (uliftYoneda.{max wFlasque v}.obj U ⋙
        AddCommGrpCat.free ⟶ F.obj) :=
    (sheafificationAdjunction J
      AddCommGrpCat.{max wFlasque v}).homEquiv _ _
  let e₂ :
      (uliftYoneda.{max wFlasque v}.obj U ⋙
          AddCommGrpCat.free ⟶ F.obj) ≃
        (uliftYoneda.{max wFlasque v}.obj U ⟶
          F.obj ⋙ forget AddCommGrpCat.{max wFlasque v}) :=
    ((AddCommGrpCat.adj).whiskerRight (Opens X)ᵒᵖ).homEquiv _ _
  exact e₁.trans (e₂.trans CategoryTheory.uliftYonedaEquiv)

/--
%%handwave
name:
  Naturality of the sheaf-section generator correspondence
statement:
  Let \(U\to V\) be an inclusion of opens and let \(G_V\to F\) be a morphism
  from the sheafified free representable generator.  Under the canonical
  correspondence
  \(\operatorname{Hom}(G_U,F)\cong F(U)\), precomposition with
  \(G_U\to G_V\) corresponds to restricting the section of \(F(V)\) to
  \(F(U)\).
proof:
  Successively use naturality of the sheafification adjunction, naturality of
  the free-forgetful adjunction, and naturality of the Yoneda correspondence.
-/
private lemma sheafSectionGeneratorHomEquiv_map
    (X : TopCat.{v}) {U V : Opens X}
    [HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    (f : U ⟶ V)
    (F : Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v})
    (g : sheafSectionGenerator X V ⟶ F) :
    sheafSectionGeneratorHomEquiv X U F (sheafSectionGeneratorMap X f ≫ g) =
      F.obj.map f.op (sheafSectionGeneratorHomEquiv X V F g) := by
  let η := Functor.whiskerRight
    (uliftYoneda.{max wFlasque v}.map f) AddCommGrpCat.free
  let e₁U : (sheafSectionGenerator X U ⟶ F) ≃
      (uliftYoneda.{max wFlasque v}.obj U ⋙
        AddCommGrpCat.free ⟶ F.obj) :=
    (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}).homEquiv _ _
  let e₁V : (sheafSectionGenerator X V ⟶ F) ≃
      (uliftYoneda.{max wFlasque v}.obj V ⋙
        AddCommGrpCat.free ⟶ F.obj) :=
    (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}).homEquiv _ _
  let e₂U :
      (uliftYoneda.{max wFlasque v}.obj U ⋙
          AddCommGrpCat.free ⟶ F.obj) ≃
        (uliftYoneda.{max wFlasque v}.obj U ⟶
          F.obj ⋙ forget AddCommGrpCat.{max wFlasque v}) :=
    ((AddCommGrpCat.adj).whiskerRight (Opens X)ᵒᵖ).homEquiv _ _
  let e₂V :
      (uliftYoneda.{max wFlasque v}.obj V ⋙
          AddCommGrpCat.free ⟶ F.obj) ≃
        (uliftYoneda.{max wFlasque v}.obj V ⟶
          F.obj ⋙ forget AddCommGrpCat.{max wFlasque v}) :=
    ((AddCommGrpCat.adj).whiskerRight (Opens X)ᵒᵖ).homEquiv _ _
  have h₁ : e₁U (sheafSectionGeneratorMap X f ≫ g) = η ≫ e₁V g := by
    simpa [e₁U, e₁V, sheafSectionGeneratorMap, η] using
      (sheafificationAdjunction (Opens.grothendieckTopology X)
        AddCommGrpCat.{max wFlasque v}).homEquiv_naturality_left η g
  have h₂ :
      e₂U (η ≫ e₁V g) =
        uliftYoneda.map f ≫ e₂V (e₁V g) := by
    simpa [e₂U, e₂V, η] using
      (((AddCommGrpCat.adj).whiskerRight (Opens X)ᵒᵖ).homEquiv_naturality_left
        (uliftYoneda.map f) (e₁V g))
  dsimp [sheafSectionGeneratorHomEquiv]
  change
    uliftYonedaEquiv
        (e₂U (e₁U (sheafSectionGeneratorMap X f ≫ g))) =
      ((F.obj ⋙ forget AddCommGrpCat.{max wFlasque v}).map f.op)
        (uliftYonedaEquiv (e₂V (e₁V g)))
  rw [CategoryTheory.uliftYonedaEquiv_naturality]
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
    [HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    (F : Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v})
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
  Exactness of sections of an exact presheaf sequence
statement:
  If $\mathcal F\to\mathcal G\to\mathcal H$ is an exact sequence of
  presheaves of abelian groups, then
  $\mathcal F(U)\to\mathcal G(U)\to\mathcal H(U)$ is exact for every open
  subset $U$, without any restriction on the coefficient universe.
proof:
  Evaluation on an open set is an exact functor because limits and colimits
  of presheaves are computed objectwise.
-/
private theorem presheaf_sections_exact_of_exact
    (X : TopCat.{v}) {U : Opens X}
    {S : ShortComplex
      (TopCat.Presheaf AddCommGrpCat.{max wFlasque v} X)}
    (hS : S.Exact) {s : S.X₂.obj (op U)}
    (h : S.g.app (op U) s = 0) :
    ∃ t : S.X₁.obj (op U), S.f.app (op U) t = s := by
  let ev :
      TopCat.Presheaf AddCommGrpCat.{max wFlasque v} X ⥤
        AddCommGrpCat.{max wFlasque v} :=
    { obj := fun P => P.obj (op U)
      map := fun f => f.app (op U)
      map_id := by intros; rfl
      map_comp := by intros; rfl }
  letI : ev.Additive := by
    constructor
    intro P Q f g
    rfl
  letI : PreservesFiniteLimits ev := by
    change PreservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ
        AddCommGrpCat.{max wFlasque v}).obj (op U))
    infer_instance
  letI : PreservesFiniteColimits ev := by
    change PreservesFiniteColimits
      ((evaluation (Opens X)ᵒᵖ
        AddCommGrpCat.{max wFlasque v}).obj (op U))
    infer_instance
  exact
    (ShortComplex.ab_exact_iff (S.map ev)).mp
      (((Functor.exact_tfae ev).out 1 3 rfl rfl).mpr
        ⟨inferInstance, inferInstance⟩ S hS) _ h

/--
%%handwave
name:
  Exactness of sections of a left-exact sheaf sequence
statement:
  If $\mathcal F\to\mathcal G\to\mathcal H$ is exact and the first arrow is
  a monomorphism, then every section of $\mathcal G(U)$ killed in
  $\mathcal H(U)$ comes from a section of $\mathcal F(U)$, in arbitrary
  coefficient universe.
proof:
  Forget to presheaves; the forgetful functor preserves finite limits, so the
  resulting presheaf sequence is exact, and then evaluate it on $U$.
-/
private theorem sheaf_sections_exact_of_left_exact
    (X : TopCat.{v}) {U : Opens X}
    [HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    {S : ShortComplex
      (Sheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{max wFlasque v})}
    (hS : S.Exact) (hf : Mono S.f)
    (s : S.X₂.obj.obj (op U))
    (h : S.g.hom.app (op U) s = 0) :
    ∃ t : S.X₁.obj.obj (op U), S.f.hom.app (op U) t = s := by
  letI : Abelian
      (Sheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{max wFlasque v}) :=
    CategoryTheory.sheafIsAbelian
  let forgetSheaf :=
    sheafToPresheaf
      (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}
  letI : forgetSheaf.Additive := by
    constructor
    intro P Q f g
    ext V
    rfl
  exact
    presheaf_sections_exact_of_exact X
      (((Functor.preservesFiniteLimits_tfae
        forgetSheaf).out
        1 3 rfl rfl).mpr inferInstance S ⟨hS, hf⟩).left h

/--
%%handwave
name:
  Universe-lifted ordinary point of the open-set site
statement:
  Every point $x$ of a topological space defines a point of its open-set site
  whose fiber on an open $U$ is the universe lift of the proposition
  $x\in U$.
proof:
  Neighborhoods containing $x$ are cofiltered under intersection.  A covering
  sieve is jointly surjective on this fiber because it contains a neighborhood
  of every point of the covered open set.
-/
private noncomputable def flasqueAcyclicityPoint
    (X : TopCat.{v}) (x : X) :
    GrothendieckTopology.Point.{max wFlasque v}
      (Opens.grothendieckTopology X) where
  fiber :=
    { obj := fun U => ULift.{max wFlasque v} (PLift (x ∈ U))
      map := fun {U V} f =>
        ↾fun h : ULift.{max wFlasque v} (PLift (x ∈ U)) =>
          (⟨⟨leOfHom f h.down.down⟩⟩ :
            ULift.{max wFlasque v} (PLift (x ∈ V))) }
  isCofiltered :=
    { nonempty := ⟨⊤, ⟨⟨by simp⟩⟩⟩
      cone_objs := by
        rintro ⟨U, ⟨⟨hU⟩⟩⟩ ⟨V, ⟨⟨hV⟩⟩⟩
        exact
          ⟨⟨U ⊓ V, ⟨⟨⟨hU, hV⟩⟩⟩⟩,
            ⟨homOfLE (by simp), rfl⟩,
            ⟨homOfLE (by simp), rfl⟩, ⟨⟩⟩
      cone_maps _ _ _ _ := ⟨_, 𝟙 _, rfl⟩ }
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective := by
    rintro U R hR ⟨⟨hU⟩⟩
    obtain ⟨V, f, hf, hV⟩ := hR x hU
    exact ⟨_, _, hf, ⟨⟨hV⟩⟩, rfl⟩

/--
%%handwave
name:
  Epimorphisms of abelian sheaves are locally surjective in arbitrary universe
statement:
  Let $\mathcal F\to\mathcal G$ be an epimorphism of abelian sheaves on a
  topological space.  For $s\in\mathcal G(U)$ and $x\in U$, there are an open
  neighborhood $x\in V\subseteq U$ and $t\in\mathcal F(V)$ whose image is
  $s|_V$, even when the coefficient groups live in a larger universe than the
  space.
proof:
  Apply the sheaf-fiber functor at the universe-lifted ordinary point $x$.
  This functor preserves epimorphisms, so the germ of $s$ has a preimage.
  Represent that germ on a neighborhood and use equality in the filtered
  colimit defining the fiber to shrink until the two representative sections
  agree.
-/
private theorem epi_sheaf_hom_locally_surjective
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    {F G : Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}}
    (f : F ⟶ G) [Epi f] (U : Opens X) (s : G.obj.obj (op U))
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (_ : V ≤ U) (t : F.obj.obj (op V)),
      f.hom.app (op V) t = s |_ V ∧ x ∈ V := by
  let Φ := flasqueAcyclicityPoint.{v, wFlasque} X x
  let SF := Φ.sheafFiber (A := AddCommGrpCat.{max wFlasque v})
  haveI : Epi (SF.map f) := by
    apply Functor.map_epi
  let xU : Φ.fiber.obj U := ⟨⟨hx⟩⟩
  let sFiber : SF.obj G := Φ.toPresheafFiber U xU G.obj s
  obtain ⟨q, hq⟩ :=
    (AddCommGrpCat.epi_iff_surjective (SF.map f)).mp
      inferInstance sFiber
  change Φ.presheafFiber.map f.hom q = sFiber at hq
  rcases Φ.toPresheafFiber_jointly_surjective q with
    ⟨V, xV, t, ht⟩
  have hxV : x ∈ V := by
    change ULift.{max wFlasque v} (PLift (x ∈ V)) at xV
    exact xV.down.down
  let T : Opens X := V ⊓ U
  let j : T ⟶ V := homOfLE inf_le_left
  let k : T ⟶ U := homOfLE inf_le_right
  let xT : Φ.fiber.obj T := ⟨⟨hxV, hx⟩⟩
  have hmapj : Φ.fiber.map j xT = xV := by rfl
  have hmapk : Φ.fiber.map k xT = xU := by rfl
  have hleft :
      Φ.toPresheafFiber T xT G.obj
          (G.obj.map j.op (f.hom.app (op V) t)) =
        Φ.presheafFiber.map f.hom q := by
    calc
      _ = Φ.toPresheafFiber V (Φ.fiber.map j xT) G.obj
          (f.hom.app (op V) t) :=
        Φ.toPresheafFiber_w_apply j xT G.obj _
      _ = Φ.toPresheafFiber V xV G.obj
          (f.hom.app (op V) t) := by rw [hmapj]
      _ = Φ.presheafFiber.map f.hom
          (Φ.toPresheafFiber V xV F.obj t) :=
        (Φ.toPresheafFiber_naturality_apply f.hom V xV t).symm
      _ = Φ.presheafFiber.map f.hom q := by
        exact congrArg (fun z => Φ.presheafFiber.map f.hom z) ht
  have hright :
      Φ.toPresheafFiber T xT G.obj (G.obj.map k.op s) =
        sFiber := by
    calc
      _ = Φ.toPresheafFiber U (Φ.fiber.map k xT) G.obj s :=
        Φ.toPresheafFiber_w_apply k xT G.obj s
      _ = Φ.toPresheafFiber U xU G.obj s := by rw [hmapk]
      _ = sFiber := rfl
  have heqFiber :
      Φ.toPresheafFiber T xT G.obj
          (G.obj.map j.op (f.hom.app (op V) t)) =
        Φ.toPresheafFiber T xT G.obj (G.obj.map k.op s) :=
    hleft.trans (hq.trans hright.symm)
  rw [Φ.toPresheafFiber_eq_iff'] at heqFiber
  obtain ⟨W, l, xW, _, heq⟩ := heqFiber
  have hWU : W ≤ U := le_trans (leOfHom l) (leOfHom k)
  refine
    ⟨W, hWU, F.obj.map l.op (F.obj.map j.op t), ?_, ?_⟩
  · calc
      f.hom.app (op W)
          (F.obj.map l.op (F.obj.map j.op t)) =
          G.obj.map l.op
            (f.hom.app (op T) (F.obj.map j.op t)) :=
        NatTrans.naturality_apply f.hom l.op _
      _ = G.obj.map l.op
          (G.obj.map j.op (f.hom.app (op V) t)) := by
        rw [NatTrans.naturality_apply f.hom j.op t]
      _ = G.obj.map l.op (G.obj.map k.op s) := heq
      _ = s |_ W := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
  · change ULift.{max wFlasque v} (PLift (x ∈ W)) at xW
    exact xW.down.down

/--
%%handwave
name:
  Partial lifts of a section through a sheaf morphism
statement:
  Given a morphism $\mathcal F\to\mathcal G$ and a section
  $s\in\mathcal G(U)$, a partial lift consists of an open subset $V\subseteq U$
  and a section of $\mathcal F(V)$ mapping to the restriction of $s$.
-/
private abbrev FlasquePartialLift
    (X : TopCat.{v})
    {F G : Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}}
    {U : Opens X} (g : F ⟶ G) (s : G.obj.obj (op U)) :=
  StructuredArrow ⟨op U, s⟩
    (Functor.whiskerRight g.hom
      (CategoryTheory.forget
        AddCommGrpCat.{max wFlasque v})).mapElements

set_option backward.isDefEq.respectTransparency false in
/--
%%handwave
name:
  Chains of partial section lifts have upper bounds
statement:
  Every chain of partial lifts of a section through a morphism of abelian
  sheaves admits an upper bound obtained by gluing the compatible sections
  over the union of their domains.
proof:
  The domains in a chain are nested.  The corresponding sections agree after
  restriction, so the sheaf gluing axiom produces a section on their union
  which is an upper bound.
-/
private lemma flasquePartialLift_chains_bounded
    (X : TopCat.{v})
    {F G : Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}}
    {U : Opens X} (g : F ⟶ G) (s : G.obj.obj (op U))
    (c : Set (FlasquePartialLift X g s))
    (h : IsChain (fun x y => Nonempty (y ⟶ x)) c) :
    ∃ ub, ∀ a ∈ c, Nonempty (ub ⟶ a) := by
  let f : c → Opens X := fun x => x.1.right.1.unop
  obtain ⟨t, ht, _⟩ :
      ∃! s₁, IsGluing F.obj f (fun x => x.val.right.2) s₁ := by
    refine Sheaf.existsUnique_gluing F _ _ (fun i j => ?_)
    obtain (rfl | h₁ | h₁) :
        i = j ∨ Nonempty (i.val ⟶ j.val) ∨
          Nonempty (j.val ⟶ i.val) := by
      grind [Subtype.ext_iff, h i.property j.property]
    · rfl
    all_goals
      rw [← CategoryOfElements.map_snd h₁.some.2]
      dsimp
      rw [← Functor.map_comp_apply]
      rfl
  have le₁ : iSup f ≤ U :=
    iSup_le <| fun j => leOfHom j.1.hom.1.unop
  have le₂ : ∀ i, i ∈ c → unop i.right.1 ≤ iSup f :=
    fun i hi => le_iSup f ⟨i, hi⟩
  use StructuredArrow.mk
    (CategoryOfElements.homMk _ _ (homOfLE le₁).op
      (TopCat.Sheaf.eq_app_of_locally_eq ht
        (fun i => leOfHom i.1.hom.1.unop)
        (fun i => (CategoryOfElements.map_snd i.1.hom).symm)).symm :
      ⟨op U, s⟩ ⟶
        (Functor.whiskerRight g.hom
          (CategoryTheory.forget
            AddCommGrpCat.{max wFlasque v})).mapElements.obj
          ⟨op (iSup f), t⟩)
  exact fun i hi =>
    Nonempty.intro
      (StructuredArrow.homMk
        (CategoryOfElements.homMk _ _
          (homOfLE (le₂ i hi)).op (ht ⟨i, hi⟩))
        (by cat_disch))

set_option backward.isDefEq.respectTransparency false in
/--
%%handwave
name:
  A flasque kernel makes a short exact sequence surjective on sections
statement:
  If
  $0\to\mathcal F\to\mathcal G\to\mathcal H\to0$
  is a short exact sequence of abelian sheaves and $\mathcal F$ is flasque,
  then $\mathcal G(U)\to\mathcal H(U)$ is surjective for every open $U$.
proof:
  Order partial lifts of a section by extension and use Zorn's lemma.  If a
  maximal partial lift is not defined everywhere, local surjectivity of the
  epimorphism gives another lift nearby.  Exactness identifies their
  difference with a section of the flasque kernel, which extends and lets the
  two partial lifts glue, contradicting maximality.
-/
theorem flasque_sectionsMap_epi_of_shortExact
    (X : TopCat.{v}) {U : Opens X}
    [HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    {S : ShortComplex
      (Sheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{max wFlasque v})}
    (hS : S.ShortExact) [TopCat.Sheaf.IsFlasque S.X₁] :
    Epi (S.g.hom.app (op U)) := by
  refine (AddCommGrpCat.epi_iff_surjective _).mpr (fun s => ?_)
  obtain ⟨t, ht⟩ := exists_maximal_of_chains_bounded
    (flasquePartialLift_chains_bounded X S.g s)
    (fun ⟨f⟩ ⟨g⟩ => ⟨g ≫ f⟩)
  have tle : t.right.1.unop ≤ U := leOfHom t.hom.1.unop
  have tcomp : s |_ t.right.1.unop =
      S.g.hom.app t.right.1 t.right.2 :=
    CategoryOfElements.map_snd t.hom
  have hUt : U ≤ t.right.1.unop := by
    intro x hx
    letI : Epi S.g := hS.epi_g
    obtain ⟨W, Wle, t₁, ht₁, hW⟩ :=
      epi_sheaf_hom_locally_surjective X S.g U s x hx
    let t₂ :=
      t.right.2 |_ (t.right.1.unop ⊓ W) -
        t₁ |_ (t.right.1.unop ⊓ W)
    have ht₂ :
        (S.g.hom.app (op (t.right.1.unop ⊓ W))) t₂ = 0 := by
      simp only [map_sub, map_restrict, ← tcomp, ht₁, t₂]
      rw [sub_eq_zero]
      exact
        (restrict_restrict (F := S.X₃.obj)
          inf_le_left tle s).trans
          (restrict_restrict (F := S.X₃.obj)
            inf_le_right Wle s).symm
    obtain ⟨t₃, ht₃⟩ :=
      sheaf_sections_exact_of_left_exact X hS.1 hS.2 t₂ ht₂
    obtain ⟨t₄, (ht₄ :
        t₄ |_ (t.right.1.unop ⊓ W) = t₃)⟩ :=
      (AddCommGrpCat.epi_iff_surjective
        (S.X₁.obj.map (homOfLE inf_le_right).op)).mp
          inferInstance t₃
    let f : Fin 2 → Opens X := ![t.right.1.unop, W]
    let sf : (i : Fin 2) → S.X₂.obj.obj (op (f i))
      | 0 => t.right.2
      | 1 => t₁ + (S.f.hom.app (op W)) t₄
    have hcompat :
        sf 0 |_ (t.right.1.unop ⊓ W) =
          sf 1 |_ (t.right.1.unop ⊓ W) := by
      dsimp [sf, f]
      simp only [restrict_sum, ← map_restrict, ht₄, ht₃, t₂,
        add_sub_cancel]
    obtain ⟨t₅, ht₅, _⟩ :
        ∃! t₅, IsGluing S.X₂.obj f sf t₅ := by
      apply Sheaf.existsUnique_gluing
      simp only [IsCompatible, Fin.forall_fin_two]
      refine ⟨⟨rfl, hcompat⟩, Eq.symm ?_, rfl⟩
      apply_fun
        (fun s' =>
          restrictOpen s' (W ⊓ t.right.1.unop)
            (le_of_eq (inf_comm _ _))) at hcompat
      rw [restrict_restrict, restrict_restrict] at hcompat
      exact hcompat
    have le : iSup f ≤ U :=
      iSup_le_iff.mpr (Fin.forall_fin_two.mpr ⟨tle, Wle⟩)
    let t₆ : FlasquePartialLift X S.g s :=
      StructuredArrow.mk
        (S := ⟨op U, s⟩)
        (T := (Functor.whiskerRight S.g.hom
          (CategoryTheory.forget
            AddCommGrpCat.{max wFlasque v})).mapElements)
        (Y := ⟨op (iSup f), t₅⟩) <|
        CategoryOfElements.homMk _ _ (homOfLE le).op (by
          refine
            (TopCat.Sheaf.eq_app_of_locally_eq ht₅
              (by
                rw [Fin.forall_fin_two]
                exact ⟨tle, Wle⟩) ?_).symm
          rw [Fin.forall_fin_two]
          refine ⟨tcomp.symm, ?_⟩
          simp only [Fin.isValue, Functor.comp_obj, map_add,
            homOfLE_leOfHom, sf, f]
          have hzero :
              S.f.hom.app (op W) ≫
                  S.g.hom.app (op W) =
                0 := by
            rw [← NatTrans.comp_app,
              ← ObjectProperty.FullSubcategory.comp_hom, S.zero]
            rfl
          simp [← CategoryTheory.comp_apply, hzero, ht₁]
          rfl)
    have ht₆ : Nonempty (t₆ ⟶ t) :=
      Nonempty.intro
        (StructuredArrow.homMk
          (CategoryOfElements.homMk _ _
            (homOfLE (le_iSup f 0)).op (ht₅ 0))
          (by cat_disch))
    exact
      leOfHom ((ht t₆) ht₆).some.right.1.unop
        ((le_iSup f 1) hW)
  exact ⟨t.right.2 |_ U, by
    simp [map_restrict, ← tcomp, restrict_restrict]⟩

/--
%%handwave
name:
  The quotient of two flasque sheaves is flasque
statement:
  In a short exact sequence of abelian sheaves, if the first and second
  sheaves are flasque, then the third sheaf is flasque.
proof:
  Lift a section of the quotient over the larger open using surjectivity on
  sections, extend its lift by flasqueness of the middle sheaf, and descend
  the extension to the quotient.
-/
theorem isFlasque_of_shortExact_of_isFlasque₁₂
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    {S : ShortComplex
      (Sheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{max wFlasque v})}
    (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque S.X₁]
    [TopCat.Sheaf.IsFlasque S.X₂] :
    TopCat.Sheaf.IsFlasque S.X₃ where
  epi {U V} i := by
    have hcomp :
        Epi (S.g.hom.app U ≫ S.X₃.obj.map i) := by
      rw [← S.g.hom.naturality i]
      exact CategoryTheory.epi_comp' inferInstance
        (flasque_sectionsMap_epi_of_shortExact X hS)
    exact CategoryTheory.epi_of_epi
      (S.g.hom.app U) (S.X₃.obj.map i)

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
    [HasWeakSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    [HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    {S : ShortComplex
      (Sheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{max wFlasque v})}
    (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque S.X₁] :
    Epi ((Sheaf.Γ (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}).map S.g) := by
  let J := Opens.grothendieckTopology X
  let Γ :
      Sheaf J AddCommGrpCat.{max wFlasque v} ⥤
        AddCommGrpCat.{max wFlasque v} :=
    Sheaf.Γ J AddCommGrpCat.{max wFlasque v}
  letI : OrderTop (Opens X) :=
    { top := (⊤ : Opens X)
      le_top := fun _ => by
        intro _ _
        trivial }
  let sectionsTop :
      Sheaf J AddCommGrpCat.{max wFlasque v} ⥤
        AddCommGrpCat.{max wFlasque v} :=
    (CategoryTheory.sheafSections J
      AddCommGrpCat.{max wFlasque v}).obj
      (op (⊤_ (Opens X)))
  let η : Γ ≅ sectionsTop :=
    CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (J := J) (A := AddCommGrpCat.{max wFlasque v})
      (T := (⊤_ (Opens X))) terminalIsTerminal
  have hsections : Epi (sectionsTop.map S.g) := by
    change Epi (S.g.hom.app (op (⊤_ (Opens X))))
    exact flasque_sectionsMap_epi_of_shortExact
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
    [HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    [HasExt.{max wFlasque v}
      (Sheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{max wFlasque v})]
    (F : Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v})
    [Injective F] :
    ∀ q : ℕ, 0 < q → Subsingleton (F.H q) := by
  intro q hq
  cases q with
  | zero =>
      exact (Nat.not_lt_zero 0 hq).elim
  | succ q =>
      change Subsingleton
        (CategoryTheory.Abelian.Ext ((constantSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{max wFlasque v}).obj
            (AddCommGrpCat.of (ULift.{max wFlasque v} ℤ))) F (q + 1))
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
    [HasWeakSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    [HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v}]
    [HasExt.{max wFlasque v}
      (Sheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{max wFlasque v})]
    (F : Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{max wFlasque v})
    [TopCat.Sheaf.IsFlasque F] :
    ∀ q : ℕ, 0 < q → Subsingleton (F.H q) := by
  let J := Opens.grothendieckTopology X
  letI : IsGrothendieckAbelian.{max wFlasque v}
      (Sheaf J AddCommGrpCat.{max wFlasque v}) :=
    CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall
      J AddCommGrpCat.{max wFlasque v}
  suffices
      ∀ q : ℕ, 0 < q →
        ∀ (G : Sheaf J AddCommGrpCat.{max wFlasque v}),
          TopCat.Sheaf.IsFlasque G →
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
          let S :
              ShortComplex
                (Sheaf J AddCommGrpCat.{max wFlasque v}) :=
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
            isFlasque_of_shortExact_of_isFlasque₁₂ (X := X) hS
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
                  Epi ((Sheaf.Γ J
                    AddCommGrpCat.{max wFlasque v}).map S.g) :=
                globalSections_map_epi_of_shortExact_of_flasque_left
                  (X := X) hS
              have hcoker :
                  IsZero
                    (cokernel
                      ((Sheaf.Γ J
                        AddCommGrpCat.{max wFlasque v}).map S.g)) :=
                isZero_cokernel_of_epi _
              haveI hcoker_subsingleton :
                  Subsingleton
                    (↥(cokernel
                      ((Sheaf.Γ J
                        AddCommGrpCat.{max wFlasque v}).map S.g))) :=
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

/--
%%handwave
name:
  Global sheafified singular cochains compute real constant-sheaf cohomology
statement:
  Let $X$ be a paracompact Hausdorff locally contractible space such that
  every open subspace of $X$ is paracompact.  Then, in every degree $n$, the
  cohomology of the global sections of the sheafified real
  singular-cochain complex is additively isomorphic to
  $H^n(X;\underline{\mathbb R})$.
proof:
  The standard augmentation of the sheafified singular-cochain complex is an
  exact resolution of the constant real sheaf.  Each term is flasque by the
  sectionwise surjectivity of singular-cochain sheafification, hence acyclic.
  Apply the acyclic-resolution comparison theorem.
-/
theorem realSingularCochainSheafGlobalSectionsCohomology_nonempty_addEquiv_realConstantSheafCohomology_of_open_paracompact
    (X : TopCat.{v}) [T2Space X] [ParacompactSpace X]
    (hopen : ∀ V : Opens X, ParacompactSpace V)
    (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) :
    Nonempty
      (↥((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (realSingularCochainSheafComplex X)).homology n) ≃+
        RealConstantSheafCohomology X n) := by
  rcases
      exists_sheafifiedOpenRealSingularCochainSheafAugmentation_with_resolution_properties
        X hloc with
    ⟨ε, hε, _hscalar, hexact_zero, hmono, hexact_pos⟩
  have hacyclic :
      ∀ p q : ℕ, 0 < q →
        Subsingleton (((realSingularCochainSheafComplex X).X p).H q) := by
    intro p q hq
    letI :
        TopCat.Sheaf.IsFlasque
          ((realSingularCochainSheafComplex X).X p) :=
      realSingularCochainSheafComplex_isFlasque_of_open_paracompact
        X hopen p
    exact
      sheafCohomology_subsingleton_of_flasque
        X ((realSingularCochainSheafComplex X).X p) q hq
  exact
    CategoryTheory.Sheaf.globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution
      (F := RealConstantAddSheaf X)
      (K := realSingularCochainSheafComplex X)
      ε hε hexact_zero hmono hexact_pos hacyclic n

/--
%%handwave
name:
  The singular acyclic-resolution comparison respects real scalars
statement:
  Under the hypotheses that $X$ is paracompact, Hausdorff and locally
  contractible and that every open subspace of $X$ is paracompact, the
  additive equivalence from the cohomology of global sheafified real singular
  cochains to $H^n(X;\underline{\mathbb R})$ can be chosen to intertwine
  cochainwise multiplication by every $r\in\mathbb R$ with multiplication by
  $r$ on constant-sheaf cohomology.
proof:
  Apply the simultaneous naturality form of the acyclic-resolution comparison
  to the family of scalar endomorphisms indexed by $\mathbb R$.  Scalar
  multiplication commutes with the standard augmentation, and the target
  action is the defining postcomposition action on constant-sheaf
  cohomology.
-/
theorem exists_realSingularCochainSheafGlobalSectionsCohomology_addEquiv_realConstantSheafCohomology_with_map_smul_of_open_paracompact
    (X : TopCat.{v}) [T2Space X] [ParacompactSpace X]
    (hopen : ∀ V : Opens X, ParacompactSpace V)
    (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) :
    ∃ e :
      ↥((((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (realSingularCochainSheafComplex X)).homology n) ≃+
        RealConstantSheafCohomology X n,
      ∀ (r : ℝ)
        (x :
          ↥((((Sheaf.Γ (Opens.grothendieckTopology X)
              AddCommGrpCat.{v}).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj
              (realSingularCochainSheafComplex X)).homology n)),
        e ((HomologicalComplex.homologyMap
              (((Sheaf.Γ (Opens.grothendieckTopology X)
                  AddCommGrpCat.{v}).mapHomologicalComplex
                    (ComplexShape.up ℕ)).map
                (sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r))
              n) x) =
          r • e x := by
  rcases
      exists_sheafifiedOpenRealSingularCochainSheafAugmentation_with_resolution_properties
        X hloc with
    ⟨ε, hε, hscalar, hexact_zero, hmono, hexact_pos⟩
  have hacyclic :
      ∀ p q : ℕ, 0 < q →
        Subsingleton (((realSingularCochainSheafComplex X).X p).H q) := by
    intro p q hq
    letI :
        TopCat.Sheaf.IsFlasque
          ((realSingularCochainSheafComplex X).X p) :=
      realSingularCochainSheafComplex_isFlasque_of_open_paracompact
        X hopen p
    exact
      sheafCohomology_subsingleton_of_flasque
        X ((realSingularCochainSheafComplex X).X p) q hq
  rcases
      CategoryTheory.Sheaf.exists_globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution_with_family_map_core
          (F := RealConstantAddSheaf X)
          (K := realSingularCochainSheafComplex X)
          ε hε hexact_zero hmono hexact_pos hacyclic
          (fun r : ℝ => realConstantSheafScalarEnd X r)
          (fun r : ℝ =>
            sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r)
          hscalar n with
    ⟨e, he⟩
  refine ⟨e, ?_⟩
  intro r x
  rw [he r x]
  rfl

/--
%%handwave
name:
  Cochains dual to a real chain complex
statement:
  For a nonnegatively graded chain complex $K_\bullet$ of real vector spaces,
  its dual cochain complex has terms
  $K^n=\operatorname{Hom}_{\mathbb R}(K_n,\mathbb R)$ and coboundary given by
  precomposition with the boundary of $K_\bullet$.
-/
abbrev RealChainCochainComplex
    (K : ChainComplex (ModuleCat.{v} ℝ) ℕ) :
    CochainComplex (ModuleCat.{v} ℝ) ℕ :=
  K.linearYonedaObj ℝ realSingularChainCoefficient

/--
%%handwave
name:
  Pullback on cochains dual to a chain map
statement:
  A chain map $f:K_\bullet\to L_\bullet$ induces the cochain map
  $f^*:\operatorname{Hom}_{\mathbb R}(L_\bullet,\mathbb R)\to
  \operatorname{Hom}_{\mathbb R}(K_\bullet,\mathbb R)$ by precomposition.
proof:
  Apply the contravariant real-linear Hom functor degreewise and pass from
  complexes in the opposite category to cochain complexes.
-/
noncomputable def realChainCochainMap
    {K L : ChainComplex (ModuleCat.{v} ℝ) ℕ} (f : K ⟶ L) :
    RealChainCochainComplex L ⟶ RealChainCochainComplex K :=
  (HomologicalComplex.unopFunctor
      (ModuleCat.{v} ℝ) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op
      (((((linearYoneda ℝ (ModuleCat.{v} ℝ)).obj
          realSingularChainCoefficient).rightOp.mapHomologicalComplex _).map f)))

/--
%%handwave
name:
  Dualization preserves chain homotopies
statement:
  If two maps $f,g:K_\bullet\to L_\bullet$ of real chain complexes are chain
  homotopic, then the induced pullback maps $f^*,g^*:L^\bullet\to K^\bullet$
  are cochain homotopic.
proof:
  Apply the contravariant real-linear dual functor to the given homotopy and
  reverse the complex shape when leaving the opposite category.
-/
theorem realChainCochainMap_homotopy
    {K L : ChainComplex (ModuleCat.{v} ℝ) ℕ}
    {f g : K ⟶ L} (H : Homotopy f g) :
    Nonempty
      (Homotopy
        (realChainCochainMap f)
        (realChainCochainMap g)) := by
  let F :=
    (((linearYoneda ℝ (ModuleCat.{v} ℝ)).obj
      realSingularChainCoefficient).rightOp)
  have Hdual :
      Homotopy
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f)
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map g) :=
    F.mapHomotopy H
  simpa [F, realChainCochainMap] using
    homotopy_unopFunctor_map_op_for_singularCohomology
      (V := ModuleCat.{v} ℝ)
      (c := ComplexShape.down ℕ)
      Hdual

/--
%%handwave
name:
  Dual of a chain-homotopy equivalence
statement:
  A chain-homotopy equivalence $K_\bullet\simeq L_\bullet$ induces a
  cochain-homotopy equivalence $L^\bullet\simeq K^\bullet$ between the
  real-linear dual complexes.
proof:
  Dualize the forward and inverse chain maps and use that dualization
  preserves both homotopies witnessing the equivalence.
-/
noncomputable def realChainCochainHomotopyEquiv
    {K L : ChainComplex (ModuleCat.{v} ℝ) ℕ}
    (e : HomotopyEquiv K L) :
    HomotopyEquiv
      (RealChainCochainComplex L)
      (RealChainCochainComplex K) where
  hom := realChainCochainMap e.hom
  inv := realChainCochainMap e.inv
  homotopyHomInvId := by
    simpa [realChainCochainMap] using
      (realChainCochainMap_homotopy e.homotopyInvHomId).some
  homotopyInvHomId := by
    simpa [realChainCochainMap] using
      (realChainCochainMap_homotopy e.homotopyHomInvId).some

/--
%%handwave
name:
  Additive-group complex underlying a dual real cochain complex
statement:
  Forgetting scalar multiplication in the dual cochain complex
  $\operatorname{Hom}_{\mathbb R}(K_\bullet,\mathbb R)$ gives a cochain
  complex of abelian groups with the same cochains and coboundaries.
-/
abbrev RealChainCochainAddComplex
    (K : ChainComplex (ModuleCat.{v} ℝ) ℕ) :
    CochainComplex AddCommGrpCat.{v} ℕ :=
  ((forget₂ (ModuleCat.{v} ℝ)
    AddCommGrpCat.{v}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    (RealChainCochainComplex K)

/--
%%handwave
name:
  Underlying additive pullback on dual cochains
statement:
  For a real chain map $f:K_\bullet\to L_\bullet$, forgetting scalars in its
  dual gives an additive cochain map $f^*:L^\bullet\to K^\bullet$.
proof:
  Apply the forgetful functor from real vector spaces to abelian groups to
  the dual cochain map.
-/
noncomputable def realChainCochainAddMap
    {K L : ChainComplex (ModuleCat.{v} ℝ) ℕ} (f : K ⟶ L) :
    RealChainCochainAddComplex L ⟶ RealChainCochainAddComplex K :=
  ((forget₂ (ModuleCat.{v} ℝ)
    AddCommGrpCat.{v}).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
    (realChainCochainMap f)

/--
%%handwave
name:
  Pullback on dual cochains reverses composition
statement:
  For real chain maps $K_\bullet\xrightarrow f L_\bullet\xrightarrow g
  M_\bullet$, one has $(g\circ f)^*=f^*\circ g^*$ on the underlying
  additive cochain complexes.
proof:
  In every degree both sides precompose a functional first with $g$ and then
  with $f$.
-/
theorem realChainCochainAddMap_comp
    {K L M : ChainComplex (ModuleCat.{v} ℝ) ℕ}
    (f : K ⟶ L) (g : L ⟶ M) :
    realChainCochainAddMap (f ≫ g) =
      realChainCochainAddMap g ≫ realChainCochainAddMap f := by
  apply HomologicalComplex.Hom.ext
  funext n
  ext α
  rfl

/--
%%handwave
name:
  Pullback along the identity chain map
statement:
  Pullback of real-valued cochains along the identity of a chain complex is
  the identity cochain map.
proof:
  Degreewise this is precomposition with the identity linear map.
-/
theorem realChainCochainAddMap_id
    (K : ChainComplex (ModuleCat.{v} ℝ) ℕ) :
    realChainCochainAddMap (𝟙 K) =
      𝟙 (RealChainCochainAddComplex K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  ext α
  rfl

/--
%%handwave
name:
  Additive dual of a chain-homotopy equivalence
statement:
  A chain-homotopy equivalence of real chain complexes induces a
  cochain-homotopy equivalence of the underlying additive dual complexes.
proof:
  Dualize the chain-homotopy equivalence and then forget real scalar
  multiplication.
-/
noncomputable def realChainCochainAddHomotopyEquiv
    {K L : ChainComplex (ModuleCat.{v} ℝ) ℕ}
    (e : HomotopyEquiv K L) :
    HomotopyEquiv
      (RealChainCochainAddComplex L)
      (RealChainCochainAddComplex K) :=
  (forget₂ (ModuleCat.{v} ℝ)
    AddCommGrpCat.{v}).mapHomotopyEquiv
      (realChainCochainHomotopyEquiv e)

/--
%%handwave
name:
  Locally vanishing cochains vanish on cover-small chains
statement:
  Let $\mathcal U=(U_i)$ be an open cover of $X$.  If an $n$-cochain
  restricts to zero on every $U_i$, then it vanishes on every singular
  $n$-chain generated by simplices contained in a member of $\mathcal U$.
proof:
  Every generator of the small-chain complex carries a chosen cover index
  and a lift to the corresponding open set.  Evaluate the cochain through
  that lift and use the assumed vanishing on the chosen open set.
-/
theorem smallCochainAddMap_eq_zero
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X)
    (n : ℕ)
    (α : (RealChainCochainAddComplex
      (realSingularChains X)).X n)
    (hα :
      ∀ i,
        (realChainCochainAddMap
          (realSingularChainFunctor.map
            (openSingularChainsInclusion X U i))).f n α = 0) :
    (realChainCochainAddMap
      (smallRealSingularChainsInclusion X U)).f n α = 0 := by
  change
    (smallRealSingularChainsInclusion X U).f n ≫ α = 0
  apply SSet.chainComplex_hom_ext
  intro σ
  let i := smallCoverIndex X U n σ
  let τ := smallSimplexLift X U n σ
  let f := openSingularChainsInclusion X U i
  have hsmall :
      (openCoverSmallSingularSet X U : SSet.{v}).ιChainComplex
          (R := realSingularChainCoefficient) σ ≫
        (smallRealSingularChainsInclusion X U).f n =
      (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ.1 := by
    dsimp only [smallRealSingularChainsInclusion]
    rw [SSet.ι_chainComplexMap_f]
    rfl
  have hlift :
      (TopCat.toSSet.obj (TopCat.of (U i) : TopCat.{v})).ιChainComplex
          (R := realSingularChainCoefficient) τ ≫
        (realSingularChainFunctor.map f).f n =
      (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ.1 := by
    change
      (TopCat.toSSet.obj (TopCat.of (U i) : TopCat.{v})).ιChainComplex
          (R := realSingularChainCoefficient) τ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f)
          realSingularChainCoefficient).f n =
      (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ.1
    rw [SSet.ι_chainComplexMap_f]
    exact congrArg
      ((TopCat.toSSet.obj X).ιChainComplex
        (R := realSingularChainCoefficient))
      (smallSimplexLift_map X U n σ)
  simp only [comp_zero]
  rw [← Category.assoc]
  calc
    ((openCoverSmallSingularSet X U : SSet.{v}).ιChainComplex
          (R := realSingularChainCoefficient) σ ≫
        (smallRealSingularChainsInclusion X U).f n) ≫ α =
      (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ.1 ≫ α := by rw [hsmall]
    _ =
      ((TopCat.toSSet.obj (TopCat.of (U i) : TopCat.{v})).ιChainComplex
          (R := realSingularChainCoefficient) τ ≫
        (realSingularChainFunctor.map f).f n) ≫ α :=
      (congrArg (fun q => q ≫ α) hlift).symm
    _ =
      (TopCat.toSSet.obj (TopCat.of (U i) : TopCat.{v})).ιChainComplex
          (R := realSingularChainCoefficient) τ ≫
        ((realSingularChainFunctor.map f).f n ≫ α) :=
      Category.assoc _ _ _
    _ =
      (TopCat.toSSet.obj (TopCat.of (U i) : TopCat.{v})).ιChainComplex
          (R := realSingularChainCoefficient) τ ≫
        (singularCochainMap ℝ f).f n α := rfl
    _ = 0 := by
      have hi := hα i
      change (singularCochainMap ℝ f).f n α = 0 at hi
      rw [hi]
      rfl

/--
%%handwave
name:
  Cover-locally zero singular cocycles are cohomologically trivial
statement:
  Let $\mathcal U=(U_i)$ cover $X$.  If a closed real singular $n$-cochain
  restricts to zero on every $U_i$, then its class in
  $H^n_{\mathrm{sing}}(X;\mathbb R)$ is zero.
proof:
  The cocycle vanishes on the subcomplex of $\mathcal U$-small chains.
  The inclusion of small chains is a chain-homotopy equivalence by iterated
  barycentric subdivision, so its dual is a cochain-homotopy equivalence and
  is injective on cohomology.
-/
theorem singularCochainAdd_homologyπ_eq_zero_of_cover_restriction_eq_zero
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X)
    (hU : IsOpenCover U) (n : ℕ)
    (z : (RealChainCochainAddComplex
      (realSingularChains X)).cycles n)
    (hz :
      ∀ i,
        (realChainCochainAddMap
          (realSingularChainFunctor.map
            (openSingularChainsInclusion X U i))).f n
            ((RealChainCochainAddComplex
              (realSingularChains X)).iCycles n z) = 0) :
    (RealChainCochainAddComplex
      (realSingularChains X)).homologyπ n z = 0 := by
  obtain ⟨e, he⟩ :=
    smallRealSingularChainsInclusion_homotopyEquiv X U hU
  let edual := realChainCochainAddHomotopyEquiv e
  have hcochain :
      edual.hom.f n
          ((RealChainCochainAddComplex
            (realSingularChains X)).iCycles n z) = 0 := by
    change
      (realChainCochainMap e.hom).f n
          ((RealChainCochainAddComplex
            (realSingularChains X)).iCycles n z) = 0
    rw [he]
    exact smallCochainAddMap_eq_zero X U n _ hz
  have hcycle :
      cyclesMap edual.hom n z = 0 := by
    apply
      (AddCommGrpCat.mono_iff_injective
        ((RealChainCochainAddComplex
          (smallRealSingularChains X U)).iCycles n)).1
        inferInstance
    calc
      (RealChainCochainAddComplex
          (smallRealSingularChains X U)).iCycles n
          (cyclesMap edual.hom n z) =
        edual.hom.f n
          ((RealChainCochainAddComplex
            (realSingularChains X)).iCycles n z) := by
            exact ConcreteCategory.congr_hom
              (cyclesMap_i edual.hom n) z
      _ = 0 := hcochain
      _ = (RealChainCochainAddComplex
          (smallRealSingularChains X U)).iCycles n 0 := by
            exact
              ((RealChainCochainAddComplex
                (smallRealSingularChains X U)).iCycles n).hom.map_zero.symm
  have hhomology :
      homologyMap edual.hom n
          ((RealChainCochainAddComplex
            (realSingularChains X)).homologyπ n z) = 0 := by
    calc
      _ = (RealChainCochainAddComplex
          (smallRealSingularChains X U)).homologyπ n
            (cyclesMap edual.hom n z) := by
              exact ConcreteCategory.congr_hom
                (homologyπ_naturality (φ := edual.hom) n) z
      _ = 0 := by rw [hcycle, map_zero]
  apply
    (AddCommGrpCat.mono_iff_injective
      (edual.toHomologyIso n).hom).1 inferInstance
  calc
    (edual.toHomologyIso n).hom
        ((RealChainCochainAddComplex
          (realSingularChains X)).homologyπ n z) =
      0 := hhomology
    _ = (edual.toHomologyIso n).hom 0 :=
      (edual.toHomologyIso n).hom.hom.map_zero.symm

/--
%%handwave
name:
  Restriction from all cochains to cover-small cochains is surjective
statement:
  Every real-valued cochain on the subcomplex of chains subordinate to an
  open family extends to a cochain on all singular chains.
proof:
  Precompose with the degreewise retraction from all singular chains onto
  the small-chain subcomplex.
-/
theorem smallCochainAddMap_surjective
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X)
    (n : ℕ) :
    Function.Surjective
      ((realChainCochainAddMap
        (smallRealSingularChainsInclusion X U)).f n) := by
  intro α
  refine ⟨smallRealSingularChainsRetract X U n ≫ α, ?_⟩
  change
    (smallRealSingularChainsInclusion X U).f n ≫
        (smallRealSingularChainsRetract X U n ≫ α) =
      α
  rw [← Category.assoc,
    smallRealSingularChainsInclusion_retract,
    Category.id_comp]

/--
%%handwave
name:
  Kernel cycles for small-chain restriction have kernel primitives
statement:
  Let $\mathcal U$ cover $X$.  If a closed real singular $(m+1)$-cochain
  vanishes on all $\mathcal U$-small chains, then it is the coboundary of an
  $m$-cochain which also vanishes on all $\mathcal U$-small chains.
proof:
  Small-chain restriction is a cochain-homotopy equivalence and is
  degreewise surjective.  First choose any global primitive.  Its restriction
  is closed; use surjectivity on cohomology to correct its cohomology class
  and degreewise surjectivity to lift a remaining small primitive.  The
  corrected global primitive restricts to zero.
-/
theorem smallCochainKernel_exists_primitive
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X)
    (hU : IsOpenCover U) (m : ℕ)
    (z : (RealChainCochainAddComplex
      (realSingularChains X)).cycles (m + 1))
    (hzsmall :
      (realChainCochainAddMap
        (smallRealSingularChainsInclusion X U)).f (m + 1)
          ((RealChainCochainAddComplex
            (realSingularChains X)).iCycles (m + 1) z) = 0) :
    ∃ β : (RealChainCochainAddComplex
        (realSingularChains X)).X m,
      (RealChainCochainAddComplex
          (realSingularChains X)).d m (m + 1) β =
        (RealChainCochainAddComplex
          (realSingularChains X)).iCycles (m + 1) z ∧
      (realChainCochainAddMap
        (smallRealSingularChainsInclusion X U)).f m β = 0 := by
  let Full :=
    RealChainCochainAddComplex (realSingularChains X)
  let Small :=
    RealChainCochainAddComplex (smallRealSingularChains X U)
  let q : Full ⟶ Small :=
    realChainCochainAddMap
      (smallRealSingularChainsInclusion X U)
  have hzclass : Full.homologyπ (m + 1) z = 0 := by
    apply
      singularCochainAdd_homologyπ_eq_zero_of_cover_restriction_eq_zero
        X U hU (m + 1) z
    intro i
    change
      (realChainCochainAddMap
        (realSingularChainFunctor.map
          (openSingularChainsInclusion X U i))).f (m + 1)
        (Full.iCycles (m + 1) z) = 0
    have hfactor :
        realSingularChainFunctor.map
            (openSingularChainsInclusion X U i) =
          SSet.chainComplexMap (openSingularChainsToSmall X U i)
              realSingularChainCoefficient ≫
            smallRealSingularChainsInclusion X U := by
      apply HomologicalComplex.Hom.ext
      funext n
      exact (openSingularChainsCompatibility X U i n).symm
    have hmaps :
        realChainCochainAddMap
            (realSingularChainFunctor.map
              (openSingularChainsInclusion X U i)) =
          q ≫
            realChainCochainAddMap
              (SSet.chainComplexMap (openSingularChainsToSmall X U i)
                realSingularChainCoefficient) := by
      rw [hfactor]
      exact realChainCochainAddMap_comp
        (SSet.chainComplexMap (openSingularChainsToSmall X U i)
          realSingularChainCoefficient)
        (smallRealSingularChainsInclusion X U)
    rw [hmaps]
    change
      (realChainCochainAddMap
          (SSet.chainComplexMap (openSingularChainsToSmall X U i)
            realSingularChainCoefficient)).f (m + 1)
        (q.f (m + 1) (Full.iCycles (m + 1) z)) = 0
    rw [hzsmall, map_zero]
  obtain ⟨a, ha⟩ :=
    cochainComplex_addCommGrp_exists_preimage_of_homologyπ_eq_zero
      (K := Full) m z hzclass
  have hqa_closed :
      Small.d m (m + 1) (q.f m a) = 0 := by
    calc
      _ = q.f (m + 1) (Full.d m (m + 1) a) := by
            exact ConcreteCategory.congr_hom (q.comm m (m + 1)) a
      _ = q.f (m + 1) (Full.iCycles (m + 1) z) := by rw [ha]
      _ = 0 := hzsmall
  have hqa_closed_sc :
      (Small.sc m).g (q.f m a) = 0 := by
    have hnext :
        (ComplexShape.up ℕ).next m = m + 1 :=
      (ComplexShape.up ℕ).next_eq' (by
        simp [ComplexShape.up_Rel])
    change Small.d m ((ComplexShape.up ℕ).next m) (q.f m a) = 0
    rw [hnext]
    exact hqa_closed
  let za : Small.cycles m :=
    (Small.sc m).abCyclesIso.inv ⟨q.f m a, hqa_closed_sc⟩
  have hza_i : Small.iCycles m za = q.f m a := by
    exact ShortComplex.abCyclesIso_inv_apply_iCycles
      (Small.sc m) ⟨q.f m a, hqa_closed_sc⟩
  obtain ⟨e, he⟩ :=
    smallRealSingularChainsInclusion_homotopyEquiv X U hU
  let edual := realChainCochainAddHomotopyEquiv e
  have hedual : edual.hom = q := by
    dsimp [edual, realChainCochainAddHomotopyEquiv,
      realChainCochainHomotopyEquiv,
      realChainCochainAddMap, q]
    rw [he]
  let xFull : Full.homology m :=
    (edual.toHomologyIso m).inv (Small.homologyπ m za)
  obtain ⟨ζ, hζ⟩ :=
    (AddCommGrpCat.epi_iff_surjective (Full.homologyπ m)).1
      inferInstance xFull
  have hζclass :
      homologyMap q m (Full.homologyπ m ζ) =
        Small.homologyπ m za := by
    calc
      _ = homologyMap q m xFull := by rw [hζ]
      _ = (edual.toHomologyIso m).hom xFull := by
            change homologyMap q m xFull =
              homologyMap edual.hom m xFull
            rw [hedual]
      _ = Small.homologyπ m za :=
        (edual.toHomologyIso m).inv_hom_id_apply _
  cases m with
  | zero =>
      have hcycles :
          cyclesMap q 0 ζ = za := by
        apply
          (AddCommGrpCat.mono_iff_injective
            (Small.homologyπ 0)).1 inferInstance
        calc
          Small.homologyπ 0 (cyclesMap q 0 ζ) =
              homologyMap q 0 (Full.homologyπ 0 ζ) := by
                exact (ConcreteCategory.congr_hom
                  (homologyπ_naturality (φ := q) 0) ζ).symm
          _ = Small.homologyπ 0 za := hζclass
      let β : Full.X 0 := a - Full.iCycles 0 ζ
      refine ⟨β, ?_, ?_⟩
      · dsimp [β]
        have hdsub :
            Full.d 0 1 (a - Full.iCycles 0 ζ) =
              Full.d 0 1 a - Full.d 0 1 (Full.iCycles 0 ζ) :=
          map_sub (ConcreteCategory.hom (Full.d 0 1)) _ _
        have hcyclezero :
            Full.d 0 1 (Full.iCycles 0 ζ) = 0 := by
          exact DFunLike.congr_fun
            (congrArg AddCommGrpCat.Hom.hom
              (Full.iCycles_d 0 1)) ζ
        calc
          _ = Full.d 0 1 a -
              Full.d 0 1 (Full.iCycles 0 ζ) := hdsub
          _ = Full.iCycles 1 z - 0 := by
                rw [ha, hcyclezero]
          _ = Full.iCycles 1 z := sub_zero _
      · dsimp [β]
        have hqsub :
            q.f 0 (a - Full.iCycles 0 ζ) =
              q.f 0 a - q.f 0 (Full.iCycles 0 ζ) :=
          map_sub (ConcreteCategory.hom (q.f 0)) _ _
        have hqi :
            q.f 0 (Full.iCycles 0 ζ) = Small.iCycles 0 za := by
          calc
            _ = Small.iCycles 0 (cyclesMap q 0 ζ) := by
                  exact (ConcreteCategory.congr_hom
                    (cyclesMap_i q 0) ζ).symm
            _ = Small.iCycles 0 za := by rw [hcycles]
        calc
          _ = q.f 0 a - q.f 0 (Full.iCycles 0 ζ) := hqsub
          _ = q.f 0 a - Small.iCycles 0 za :=
            congrArg (fun t => q.f 0 a - t) hqi
          _ = q.f 0 a - q.f 0 a :=
            congrArg (fun t => q.f 0 a - t) hza_i
          _ = 0 := sub_self _
  | succ k =>
      let zDiff : Small.cycles (k + 1) :=
        za - cyclesMap q (k + 1) ζ
      have hzDiffClass :
          Small.homologyπ (k + 1) zDiff = 0 := by
        dsimp [zDiff]
        rw [map_sub]
        have hnat :
            Small.homologyπ (k + 1)
                (cyclesMap q (k + 1) ζ) =
              homologyMap q (k + 1)
                (Full.homologyπ (k + 1) ζ) := by
          exact (ConcreteCategory.congr_hom
            (homologyπ_naturality (φ := q) (k + 1)) ζ).symm
        rw [hnat, hζclass, sub_self]
      obtain ⟨θ, hθ⟩ :=
        cochainComplex_addCommGrp_exists_preimage_of_homologyπ_eq_zero
          (K := Small) k zDiff hzDiffClass
      obtain ⟨θFull, hθFull⟩ :=
        smallCochainAddMap_surjective X U k θ
      let β : Full.X (k + 1) :=
        a - Full.iCycles (k + 1) ζ -
          Full.d k (k + 1) θFull
      refine ⟨β, ?_, ?_⟩
      · dsimp [β]
        have hdsub_outer :
            Full.d (k + 1) (k + 2)
                (a - Full.iCycles (k + 1) ζ -
                  Full.d k (k + 1) θFull) =
              Full.d (k + 1) (k + 2)
                  (a - Full.iCycles (k + 1) ζ) -
                Full.d (k + 1) (k + 2)
                  (Full.d k (k + 1) θFull) :=
          map_sub
            (ConcreteCategory.hom
              (Full.d (k + 1) (k + 2))) _ _
        have hdsub_inner :
            Full.d (k + 1) (k + 2)
                (a - Full.iCycles (k + 1) ζ) =
              Full.d (k + 1) (k + 2) a -
                Full.d (k + 1) (k + 2)
                  (Full.iCycles (k + 1) ζ) :=
          map_sub
            (ConcreteCategory.hom
              (Full.d (k + 1) (k + 2))) _ _
        have hcyclezero :
            Full.d (k + 1) (k + 2)
                (Full.iCycles (k + 1) ζ) = 0 := by
          exact DFunLike.congr_fun
            (congrArg AddCommGrpCat.Hom.hom
              (Full.iCycles_d (k + 1) (k + 2))) ζ
        have hdd :
            Full.d (k + 1) (k + 2)
                (Full.d k (k + 1) θFull) = 0 := by
          change
            (Full.d k (k + 1) ≫
              Full.d (k + 1) (k + 2)) θFull = 0
          rw [Full.d_comp_d]
          rfl
        calc
          _ = Full.d (k + 1) (k + 2)
                (a - Full.iCycles (k + 1) ζ) -
              Full.d (k + 1) (k + 2)
                (Full.d k (k + 1) θFull) := hdsub_outer
          _ = (Full.d (k + 1) (k + 2) a -
                Full.d (k + 1) (k + 2)
                  (Full.iCycles (k + 1) ζ)) -
              Full.d (k + 1) (k + 2)
                (Full.d k (k + 1) θFull) := by rw [hdsub_inner]
          _ = (Full.iCycles (k + 2) z - 0) - 0 := by
                rw [ha, hcyclezero, hdd]
          _ = Full.iCycles (k + 2) z := by
                rw [sub_zero, sub_zero]
      · dsimp [β]
        have hqsub_outer :
            q.f (k + 1)
                (a - Full.iCycles (k + 1) ζ -
                  Full.d k (k + 1) θFull) =
              q.f (k + 1)
                  (a - Full.iCycles (k + 1) ζ) -
                q.f (k + 1) (Full.d k (k + 1) θFull) :=
          map_sub (ConcreteCategory.hom (q.f (k + 1))) _ _
        have hqsub_inner :
            q.f (k + 1)
                (a - Full.iCycles (k + 1) ζ) =
              q.f (k + 1) a -
                q.f (k + 1) (Full.iCycles (k + 1) ζ) :=
          map_sub (ConcreteCategory.hom (q.f (k + 1))) _ _
        have hqi :
            q.f (k + 1) (Full.iCycles (k + 1) ζ) =
              Small.iCycles (k + 1)
                (cyclesMap q (k + 1) ζ) := by
          change
            (ConcreteCategory.hom
              (Full.iCycles (k + 1) ≫ q.f (k + 1))) ζ =
            (ConcreteCategory.hom
              (cyclesMap q (k + 1) ≫
                Small.iCycles (k + 1))) ζ
          exact (ConcreteCategory.congr_hom
            (cyclesMap_i q (k + 1)) ζ).symm
        have hqd :
            q.f (k + 1) (Full.d k (k + 1) θFull) =
              Small.d k (k + 1) θ := by
          calc
            _ = Small.d k (k + 1) (q.f k θFull) := by
                  change
                    (ConcreteCategory.hom
                      (Full.d k (k + 1) ≫
                        q.f (k + 1))) θFull =
                    (ConcreteCategory.hom
                      (q.f k ≫ Small.d k (k + 1))) θFull
                  exact (ConcreteCategory.congr_hom
                    (q.comm k (k + 1)) θFull).symm
            _ = Small.d k (k + 1) θ := by rw [hθFull]
        have hzdiff_i :
            Small.iCycles (k + 1) zDiff =
              Small.iCycles (k + 1) za -
                Small.iCycles (k + 1)
                  (cyclesMap q (k + 1) ζ) := by
          dsimp [zDiff]
          exact map_sub
            (ConcreteCategory.hom
              (Small.iCycles (k + 1))) _ _
        calc
          _ = q.f (k + 1)
                (a - Full.iCycles (k + 1) ζ) -
              q.f (k + 1) (Full.d k (k + 1) θFull) :=
            hqsub_outer
          _ = (q.f (k + 1) a -
                q.f (k + 1) (Full.iCycles (k + 1) ζ)) -
              q.f (k + 1) (Full.d k (k + 1) θFull) := by
                rw [hqsub_inner]
          _ = (Small.iCycles (k + 1) za -
                Small.iCycles (k + 1)
                  (cyclesMap q (k + 1) ζ)) -
              Small.d k (k + 1) θ := by
                rw [hza_i, hqi, hqd]
          _ = Small.iCycles (k + 1) zDiff -
              Small.d k (k + 1) θ := by rw [hzdiff_i]
          _ = 0 := by rw [hθ, sub_self]

/--
%%handwave
name:
  A top-open cocycle vanishing after sheafification is exact
statement:
  If the sheafification of a closed real singular $n$-cochain on $X$ is zero,
  then its class in $H^n_{\mathrm{sing}}(X;\mathbb R)$ is zero.
proof:
  Local injectivity of sheafification supplies an open cover on which the
  cochain restricts to zero.  Transport from the terminal open subspace to
  $X$ and apply the small-chain subdivision equivalence to this cover.
-/
theorem
    openSingularCochainTop_homologyπ_eq_zero_of_toSheafify_iCycles_eq_zero
    (X : TopCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (n : ℕ)
    (z :
      ((realSingularCochainOpenComplexFunctor X).obj
        (op (⊤ : Opens X))).cycles n)
    (hz :
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).X n)).app
          (op (⊤ : Opens X)))
        ((((realSingularCochainOpenComplexFunctor X).obj
          (op (⊤ : Opens X))).iCycles n) z) = 0) :
    (((realSingularCochainOpenComplexFunctor X).obj
      (op (⊤ : Opens X))).homologyπ n) z = 0 := by
  let T : TopCat.{v} := (Opens.toTopCat X).obj (⊤ : Opens X)
  let K := (realSingularCochainOpenComplexFunctor X).obj
    (op (⊤ : Opens X))
  let i : T ≅ X := Opens.inclusionTopIso X
  let α : K.X n := K.iCycles n z
  have hlocal :=
    addCommGrp_toSheafify_eq_zero_locally
      (X := X)
      ((realSingularCochainOpenPresheafComplex X).X n)
      (U := (⊤ : Opens X)) α hz
  choose U hUtop hxU hres using
    fun x => hlocal x (by trivial)
  have hU : IsOpenCover U := by
    apply top_unique
    intro x _hx
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  let φ : K ⟶
      RealChainCochainAddComplex (realSingularChains X) :=
    realChainCochainAddMap
      (realSingularChainFunctor.map i.inv)
  let zX : (RealChainCochainAddComplex
      (realSingularChains X)).cycles n :=
    cyclesMap φ n z
  have hzXres :
      ∀ x,
        (realChainCochainAddMap
          (realSingularChainFunctor.map
            (openSingularChainsInclusion X U x))).f n
            ((RealChainCochainAddComplex
              (realSingularChains X)).iCycles n zX) = 0 := by
    intro x
    let j : (TopCat.of (U x) : TopCat.{v}) ⟶ X :=
      openSingularChainsInclusion X U x
    let k : (Opens.toTopCat X).obj (U x) ⟶ T :=
      (Opens.toTopCat X).map (homOfLE (hUtop x))
    have hjk : j ≫ i.inv = k := by
      ext y
      apply Subtype.ext
      rfl
    calc
      (realChainCochainAddMap
          (realSingularChainFunctor.map j)).f n
          ((RealChainCochainAddComplex
            (realSingularChains X)).iCycles n zX) =
        (realChainCochainAddMap
          (realSingularChainFunctor.map j)).f n
          (φ.f n (K.iCycles n z)) := by
            exact congrArg
              (fun q =>
                (realChainCochainAddMap
                  (realSingularChainFunctor.map j)).f n q)
              (ConcreteCategory.congr_hom
                (cyclesMap_i φ n) z)
      _ = ((φ ≫
          realChainCochainAddMap
            (realSingularChainFunctor.map j)).f n)
          (K.iCycles n z) := rfl
      _ = (realChainCochainAddMap
          (realSingularChainFunctor.map (j ≫ i.inv))).f n
          (K.iCycles n z) := by
            have hmaps :
                φ ≫ realChainCochainAddMap
                    (realSingularChainFunctor.map j) =
                  realChainCochainAddMap
                    (realSingularChainFunctor.map (j ≫ i.inv)) := by
              dsimp [φ]
              calc
                _ = realChainCochainAddMap
                    (realSingularChainFunctor.map j ≫
                      realSingularChainFunctor.map i.inv) :=
                  (realChainCochainAddMap_comp
                    (realSingularChainFunctor.map j)
                    (realSingularChainFunctor.map i.inv)).symm
                _ = _ := by rw [← Functor.map_comp]
            exact congrArg
              (fun q => q.f n (K.iCycles n z)) hmaps
      _ = (realChainCochainAddMap
          (realSingularChainFunctor.map k)).f n
          (K.iCycles n z) :=
        congrArg
          (fun q =>
            (realChainCochainAddMap
              (realSingularChainFunctor.map q)).f n
                (K.iCycles n z)) hjk
      _ = 0 := by
            change
              (((realSingularCochainOpenComplexFunctor X).map
                (homOfLE (hUtop x)).op).f n) α = 0
            exact hres x
  have hzX :
      (RealChainCochainAddComplex
        (realSingularChains X)).homologyπ n zX = 0 :=
    singularCochainAdd_homologyπ_eq_zero_of_cover_restriction_eq_zero
      X U hU n zX hzXres
  have hforward :
      homologyMap φ n (K.homologyπ n z) = 0 := by
    calc
      _ = (RealChainCochainAddComplex
          (realSingularChains X)).homologyπ n
          (cyclesMap φ n z) := by
            exact ConcreteCategory.congr_hom
              (homologyπ_naturality (φ := φ) n) z
      _ = 0 := hzX
  let ψ : RealChainCochainAddComplex
      (realSingularChains X) ⟶ K :=
    realChainCochainAddMap
      (realSingularChainFunctor.map i.hom)
  have hcomp : φ ≫ ψ = 𝟙 _ := by
    dsimp [φ, ψ]
    calc
      _ = realChainCochainAddMap
          (realSingularChainFunctor.map i.hom ≫
            realSingularChainFunctor.map i.inv) :=
        (realChainCochainAddMap_comp
          (realSingularChainFunctor.map i.hom)
          (realSingularChainFunctor.map i.inv)).symm
      _ = realChainCochainAddMap
          (realSingularChainFunctor.map (i.hom ≫ i.inv)) := by
            rw [Functor.map_comp]
      _ = realChainCochainAddMap
          (𝟙 (realSingularChains T)) := by
            rw [i.hom_inv_id]
            exact congrArg realChainCochainAddMap
              (realSingularChainFunctor.map_id T)
      _ = 𝟙 _ :=
        realChainCochainAddMap_id (realSingularChains T)
  calc
    K.homologyπ n z =
        homologyMap (𝟙 K) n (K.homologyπ n z) := by
          rw [homologyMap_id]
          rfl
    _ = homologyMap (φ ≫ ψ) n (K.homologyπ n z) := by
          rw [hcomp]
    _ = homologyMap ψ n
        (homologyMap φ n (K.homologyπ n z)) := by
          rw [homologyMap_comp]
          rfl
    _ = 0 := by rw [hforward, map_zero]

/--
%%handwave
name:
  A positive kernel cocycle has a kernel primitive
statement:
  If a closed top-open real singular $(m+1)$-cochain becomes zero after
  sheafification, then it has an $m$-cochain primitive which also becomes
  zero after sheafification.
proof:
  Choose an open cover on which the cocycle vanishes.  Transport to singular
  cochains on $X$ and use the kernel primitive for restriction to cover-small
  chains.  Transport the primitive back to the terminal open.  Its restriction
  to every cover member is zero, so separatedness of the sheafification shows
  that its sheafified image is zero.
-/
theorem openSingularCochainTop_exists_kernel_primitive
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
    ∃ β :
        ((realSingularCochainOpenComplexFunctor X).obj
          (op (⊤ : Opens X))).X m,
      (((realSingularCochainOpenComplexFunctor X).obj
          (op (⊤ : Opens X))).d m (m + 1)) β =
        (((realSingularCochainOpenComplexFunctor X).obj
          (op (⊤ : Opens X))).iCycles (m + 1)) z ∧
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).X m)).app
          (op (⊤ : Opens X))) β = 0 := by
  let T : TopCat.{v} := (Opens.toTopCat X).obj (⊤ : Opens X)
  let K := (realSingularCochainOpenComplexFunctor X).obj
    (op (⊤ : Opens X))
  let XC := RealChainCochainAddComplex (realSingularChains X)
  let i : T ≅ X := Opens.inclusionTopIso X
  let α : K.X (m + 1) := K.iCycles (m + 1) z
  have hlocal :=
    addCommGrp_toSheafify_eq_zero_locally
      (X := X)
      ((realSingularCochainOpenPresheafComplex X).X (m + 1))
      (U := (⊤ : Opens X)) α hz
  choose U hUtop hxU hres using
    fun x => hlocal x (by trivial)
  have hU : IsOpenCover U := by
    apply top_unique
    intro x _hx
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  let φ : K ⟶ XC :=
    realChainCochainAddMap
      (realSingularChainFunctor.map i.inv)
  let zX : XC.cycles (m + 1) := cyclesMap φ (m + 1) z
  have hzXres :
      ∀ x,
        (realChainCochainAddMap
          (realSingularChainFunctor.map
            (openSingularChainsInclusion X U x))).f (m + 1)
            (XC.iCycles (m + 1) zX) = 0 := by
    intro x
    let j : (TopCat.of (U x) : TopCat.{v}) ⟶ X :=
      openSingularChainsInclusion X U x
    let k : (Opens.toTopCat X).obj (U x) ⟶ T :=
      (Opens.toTopCat X).map (homOfLE (hUtop x))
    have hjk : j ≫ i.inv = k := by
      ext y
      apply Subtype.ext
      rfl
    calc
      (realChainCochainAddMap
          (realSingularChainFunctor.map j)).f (m + 1)
          (XC.iCycles (m + 1) zX) =
        (realChainCochainAddMap
          (realSingularChainFunctor.map j)).f (m + 1)
          (φ.f (m + 1) (K.iCycles (m + 1) z)) := by
            exact congrArg
              (fun q =>
                (realChainCochainAddMap
                  (realSingularChainFunctor.map j)).f (m + 1) q)
              (ConcreteCategory.congr_hom
                (cyclesMap_i φ (m + 1)) z)
      _ = ((φ ≫
          realChainCochainAddMap
            (realSingularChainFunctor.map j)).f (m + 1))
          (K.iCycles (m + 1) z) := rfl
      _ = (realChainCochainAddMap
          (realSingularChainFunctor.map (j ≫ i.inv))).f (m + 1)
          (K.iCycles (m + 1) z) := by
            have hmaps :
                φ ≫ realChainCochainAddMap
                    (realSingularChainFunctor.map j) =
                  realChainCochainAddMap
                    (realSingularChainFunctor.map (j ≫ i.inv)) := by
              dsimp [φ]
              calc
                _ = realChainCochainAddMap
                    (realSingularChainFunctor.map j ≫
                      realSingularChainFunctor.map i.inv) :=
                  (realChainCochainAddMap_comp
                    (realSingularChainFunctor.map j)
                    (realSingularChainFunctor.map i.inv)).symm
                _ = _ := by rw [← Functor.map_comp]
            exact congrArg
              (fun q => q.f (m + 1) (K.iCycles (m + 1) z)) hmaps
      _ = (realChainCochainAddMap
          (realSingularChainFunctor.map k)).f (m + 1)
          (K.iCycles (m + 1) z) :=
        congrArg
          (fun q =>
            (realChainCochainAddMap
              (realSingularChainFunctor.map q)).f (m + 1)
                (K.iCycles (m + 1) z)) hjk
      _ = 0 := by
            change
              (((realSingularCochainOpenComplexFunctor X).map
                (homOfLE (hUtop x)).op).f (m + 1)) α = 0
            exact hres x
  have hzXsmall :
      (realChainCochainAddMap
        (smallRealSingularChainsInclusion X U)).f (m + 1)
          (XC.iCycles (m + 1) zX) = 0 :=
    smallCochainAddMap_eq_zero X U (m + 1) _ hzXres
  obtain ⟨βX, hβX, hβXsmall⟩ :=
    smallCochainKernel_exists_primitive
      X U hU m zX hzXsmall
  let ψ : XC ⟶ K :=
    realChainCochainAddMap
      (realSingularChainFunctor.map i.hom)
  have hcomp : φ ≫ ψ = 𝟙 _ := by
    dsimp [φ, ψ]
    calc
      _ = realChainCochainAddMap
          (realSingularChainFunctor.map i.hom ≫
            realSingularChainFunctor.map i.inv) :=
        (realChainCochainAddMap_comp
          (realSingularChainFunctor.map i.hom)
          (realSingularChainFunctor.map i.inv)).symm
      _ = realChainCochainAddMap
          (realSingularChainFunctor.map (i.hom ≫ i.inv)) := by
            rw [Functor.map_comp]
      _ = realChainCochainAddMap
          (𝟙 (realSingularChains T)) := by
            rw [i.hom_inv_id]
            exact congrArg realChainCochainAddMap
              (realSingularChainFunctor.map_id T)
      _ = 𝟙 _ :=
        realChainCochainAddMap_id (realSingularChains T)
  let β : K.X m := ψ.f m βX
  have hβboundary : K.d m (m + 1) β = K.iCycles (m + 1) z := by
    calc
      K.d m (m + 1) β =
          ψ.f (m + 1) (XC.d m (m + 1) βX) := by
            change
              (ConcreteCategory.hom
                (ψ.f m ≫ K.d m (m + 1))) βX =
              (ConcreteCategory.hom
                (XC.d m (m + 1) ≫ ψ.f (m + 1))) βX
            exact ConcreteCategory.congr_hom
              (ψ.comm m (m + 1)) βX
      _ = ψ.f (m + 1) (XC.iCycles (m + 1) zX) := by rw [hβX]
      _ = ψ.f (m + 1)
          (φ.f (m + 1) (K.iCycles (m + 1) z)) := by
            exact congrArg (fun q => ψ.f (m + 1) q)
              (ConcreteCategory.congr_hom
                (cyclesMap_i φ (m + 1)) z)
      _ = (φ ≫ ψ).f (m + 1) (K.iCycles (m + 1) z) := rfl
      _ = K.iCycles (m + 1) z := by rw [hcomp]; rfl
  have hβrestrict :
      ∀ x,
        (((realSingularCochainOpenComplexFunctor X).map
          (homOfLE (hUtop x)).op).f m) β = 0 := by
    intro x
    let j : (TopCat.of (U x) : TopCat.{v}) ⟶ X :=
      openSingularChainsInclusion X U x
    let k : (Opens.toTopCat X).obj (U x) ⟶ T :=
      (Opens.toTopCat X).map (homOfLE (hUtop x))
    have hkj : k ≫ i.hom = j := by
      ext y
      rfl
    have hjzero :
        (realChainCochainAddMap
          (realSingularChainFunctor.map j)).f m βX = 0 := by
      have hfactor :
          realSingularChainFunctor.map j =
            SSet.chainComplexMap (openSingularChainsToSmall X U x)
                realSingularChainCoefficient ≫
              smallRealSingularChainsInclusion X U := by
        apply HomologicalComplex.Hom.ext
        funext n
        exact (openSingularChainsCompatibility X U x n).symm
      have hmaps :
          realChainCochainAddMap
              (realSingularChainFunctor.map j) =
            realChainCochainAddMap
                (smallRealSingularChainsInclusion X U) ≫
              realChainCochainAddMap
                (SSet.chainComplexMap (openSingularChainsToSmall X U x)
                  realSingularChainCoefficient) := by
        rw [hfactor]
        exact realChainCochainAddMap_comp
          (SSet.chainComplexMap (openSingularChainsToSmall X U x)
            realSingularChainCoefficient)
          (smallRealSingularChainsInclusion X U)
      rw [hmaps]
      change
        (realChainCochainAddMap
          (SSet.chainComplexMap (openSingularChainsToSmall X U x)
            realSingularChainCoefficient)).f m
          ((realChainCochainAddMap
            (smallRealSingularChainsInclusion X U)).f m βX) = 0
      rw [hβXsmall, map_zero]
    change
      (realChainCochainAddMap
        (realSingularChainFunctor.map k)).f m (ψ.f m βX) = 0
    have hmaps :
        ψ ≫ realChainCochainAddMap
            (realSingularChainFunctor.map k) =
          realChainCochainAddMap
            (realSingularChainFunctor.map j) := by
      dsimp [ψ]
      calc
        _ = realChainCochainAddMap
            (realSingularChainFunctor.map k ≫
              realSingularChainFunctor.map i.hom) :=
          (realChainCochainAddMap_comp
            (realSingularChainFunctor.map k)
            (realSingularChainFunctor.map i.hom)).symm
        _ = realChainCochainAddMap
            (realSingularChainFunctor.map (k ≫ i.hom)) := by
              rw [← Functor.map_comp]
        _ = realChainCochainAddMap
            (realSingularChainFunctor.map j) :=
          congrArg
            (fun q =>
              realChainCochainAddMap
                (realSingularChainFunctor.map q)) hkj
    change (ψ ≫ realChainCochainAddMap
      (realSingularChainFunctor.map k)).f m βX = 0
    rw [hmaps]
    exact hjzero
  have hβsheaf :
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X)
        ((realSingularCochainOpenPresheafComplex X).X m)).app
          (op (⊤ : Opens X))) β = 0 := by
    apply
      realSingularCochainOpenPresheafComplex_sheafified_section_eq_of_locally_eq
        (X := X) m
    intro x _hx
    refine ⟨U x, hUtop x, hxU x, ?_⟩
    let P := (realSingularCochainOpenPresheafComplex X).X m
    let η := CategoryTheory.toSheafify
      (Opens.grothendieckTopology X) P
    have hnat := η.naturality (homOfLE (hUtop x)).op
    have happ := congrArg
      (fun f => (ConcreteCategory.hom f) β) hnat
    calc
      ((CategoryTheory.sheafify
        (Opens.grothendieckTopology X) P).map
          (homOfLE (hUtop x)).op)
        ((η.app (op (⊤ : Opens X))) β) =
          (η.app (op (U x)))
            (P.map (homOfLE (hUtop x)).op β) := by
              simpa [ConcreteCategory.comp_apply] using happ
      _ = (η.app (op (U x))) 0 := by
            apply congrArg
            change
              (((realSingularCochainOpenComplexFunctor X).map
                (homOfLE (hUtop x)).op).f m) β = 0
            exact hβrestrict x
      _ = 0 := (η.app (op (U x))).hom.map_zero
      _ = ((CategoryTheory.sheafify
        (Opens.grothendieckTopology X) P).map
          (homOfLE (hUtop x)).op) 0 := by
            exact
              ((CategoryTheory.sheafify
                (Opens.grothendieckTopology X) P).map
                  (homOfLE (hUtop x)).op).hom.map_zero.symm
  exact ⟨β, hβboundary, hβsheaf⟩

/--
%%handwave
name:
  The top-open comparison is onto in each cochain degree
statement:
  On a Hausdorff space whose whole open subspace is paracompact, every global
  section of the sheafified real singular $n$-cochains is represented by an
  ordinary singular $n$-cochain on the whole space.
proof:
  The sheafification unit is surjective over a paracompact open set.  Apply
  this to the terminal open and compose with the canonical isomorphism
  between sections over that open and global sections.
-/
theorem
    openSingularCochainTopToSheafifiedGlobalSections_f_surjective
    (X : TopCat.{v}) [T2Space X] [ParacompactSpace X]
    (hopen : ∀ V : Opens X, ParacompactSpace V)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (n : ℕ) :
    Function.Surjective
      (ConcreteCategory.hom
        ((openSingularCochainTopToSheafifiedGlobalSections X).f n)) := by
  letI : ParacompactSpace (⊤ : Opens X) := hopen ⊤
  let J := Opens.grothendieckTopology X
  letI : OrderTop (Opens X) :=
    { top := (⊤ : Opens X)
      le_top := fun _ => by
        intro _ _
        trivial }
  have hTop : IsTerminal (⊤ : Opens X) :=
    CategoryTheory.Limits.isTerminalTop
  let γ : Sheaf.Γ J AddCommGrpCat.{v} ≅
      (CategoryTheory.sheafSections J AddCommGrpCat.{v}).obj
        (op (⊤ : Opens X)) :=
    CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (J := J) (A := AddCommGrpCat.{v})
      (T := (⊤ : Opens X)) hTop
  let F := (realSingularCochainSheafComplex X).X n
  intro s
  obtain ⟨a, ha⟩ :=
    realSingularCochain_toSheafify_app_surjective_of_paracompact
      (X := X) n (⊤ : Opens X)
      ((γ.app F).hom s)
  refine ⟨a, ?_⟩
  change
    (γ.app F).inv
      (((CategoryTheory.toSheafify J
        ((realSingularCochainOpenPresheafComplex X).X n)).app
          (op (⊤ : Opens X))) a) = s
  rw [ha]
  simpa using
    ConcreteCategory.congr_hom
      (CategoryTheory.Iso.hom_inv_id (γ.app F)) s

/--
%%handwave
name:
  A surjective cochain map with acyclic kernel is a quasi-isomorphism
statement:
  Let $\varphi:K^\bullet\to L^\bullet$ be a degreewise surjective map of
  nonnegatively graded cochain complexes of abelian groups.  Suppose its
  kernel has no degree-zero cycles and every positive-degree kernel cocycle
  has a primitive lying in the kernel.  Then
  $H^n(\varphi):H^n(K)\to H^n(L)$ is bijective for every $n$.
proof:
  For injectivity, lift a primitive of the image of a cocycle and subtract
  its coboundary; the resulting kernel cocycle has a kernel primitive.  For
  surjectivity, lift a target cocycle degreewise; its coboundary is a positive
  kernel cocycle, whose kernel primitive corrects the lift to a cocycle.
-/
theorem cochainMap_homologyMap_bijective_of_surjective_kernel_acyclic
    {K L : CochainComplex Ab.{v} ℕ} (φ : K ⟶ L)
    (hsurj :
      ∀ n, Function.Surjective (ConcreteCategory.hom (φ.f n)))
    (hkernel_zero :
      ∀ z : K.cycles 0,
        φ.f 0 (K.iCycles 0 z) = 0 → z = 0)
    (hkernel_succ :
      ∀ (m : ℕ) (z : K.cycles (m + 1)),
        φ.f (m + 1) (K.iCycles (m + 1) z) = 0 →
          ∃ β : K.X m,
            K.d m (m + 1) β = K.iCycles (m + 1) z ∧
            φ.f m β = 0)
    (n : ℕ) :
    Function.Bijective
      (ConcreteCategory.hom (homologyMap φ n)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hπsurj :
        Function.Surjective
          (ConcreteCategory.hom (K.homologyπ n)) :=
      (AddCommGrpCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance
    obtain ⟨z, rfl⟩ := hπsurj x
    have hclass :
        L.homologyπ n (cyclesMap φ n z) = 0 := by
      have hnat :=
        ConcreteCategory.congr_hom
          (homologyπ_naturality φ n) z
      have hnat' :
          L.homologyπ n (cyclesMap φ n z) =
            homologyMap φ n (K.homologyπ n z) := by
        rw [ConcreteCategory.comp_apply,
          ConcreteCategory.comp_apply] at hnat
        exact hnat.symm
      exact hnat'.trans hx
    cases n with
    | zero =>
        have hzL : cyclesMap φ 0 z = 0 :=
          cochainComplex_addCommGrp_cycle_zero_of_homologyπ_zero_eq_zero
            (K := L) _ hclass
        have hφz : φ.f 0 (K.iCycles 0 z) = 0 := by
          calc
            φ.f 0 (K.iCycles 0 z) =
                L.iCycles 0 (cyclesMap φ 0 z) := by
                  exact
                    (ConcreteCategory.congr_hom
                      (cyclesMap_i φ 0) z).symm
            _ = 0 := by rw [hzL]; exact (L.iCycles 0).hom.map_zero
        rw [hkernel_zero z hφz]
        exact (K.homologyπ 0).hom.map_zero
    | succ m =>
        obtain ⟨b, hb⟩ :=
          cochainComplex_addCommGrp_exists_preimage_of_homologyπ_eq_zero
            (K := L) m (cyclesMap φ (m + 1) z) hclass
        obtain ⟨a, ha⟩ := hsurj m b
        let γ : K.X (m + 1) :=
          K.iCycles (m + 1) z - K.d m (m + 1) a
        have hγclosed : K.d (m + 1) (m + 2) γ = 0 := by
          dsimp [γ]
          rw [map_sub]
          have hzclosed :
              K.d (m + 1) (m + 2) (K.iCycles (m + 1) z) = 0 := by
            rw [← ConcreteCategory.comp_apply, K.iCycles_d]
            rfl
          rw [hzclosed]
          have hdd :
              K.d (m + 1) (m + 2) (K.d m (m + 1) a) = 0 := by
            change
              (ConcreteCategory.hom
                (K.d m (m + 1) ≫ K.d (m + 1) (m + 2))) a = 0
            rw [K.d_comp_d]
            rfl
          rw [hdd, sub_self]
        have hnext :
            (ComplexShape.up ℕ).next (m + 1) = m + 2 :=
          (ComplexShape.up ℕ).next_eq'
            (by simp [ComplexShape.up_Rel])
        have hγclosedS : (K.sc (m + 1)).g γ = 0 := by
          change K.d (m + 1) ((ComplexShape.up ℕ).next (m + 1)) γ = 0
          rw [hnext]
          exact hγclosed
        let xγ : AddMonoidHom.ker (K.sc (m + 1)).g.hom :=
          ⟨γ, hγclosedS⟩
        let zγ : K.cycles (m + 1) :=
          (K.sc (m + 1)).abCyclesIso.inv xγ
        have hzγi : K.iCycles (m + 1) zγ = γ := by
          simpa [zγ, xγ] using
            ShortComplex.abCyclesIso_inv_apply_iCycles
              (K.sc (m + 1)) xγ
        have hφγ : φ.f (m + 1) (K.iCycles (m + 1) zγ) = 0 := by
          rw [hzγi]
          dsimp [γ]
          rw [map_sub]
          have hcomm :=
            ConcreteCategory.congr_hom (φ.comm m (m + 1)) a
          have hcomm' :
              L.d m (m + 1) (φ.f m a) =
                φ.f (m + 1) (K.d m (m + 1) a) := by
            change
              L.d m (m + 1) (φ.f m a) =
                φ.f (m + 1) (K.d m (m + 1) a) at hcomm
            exact hcomm
          have hφz :
              φ.f (m + 1) (K.iCycles (m + 1) z) =
                L.iCycles (m + 1) (cyclesMap φ (m + 1) z) := by
            exact
              (ConcreteCategory.congr_hom
                (cyclesMap_i φ (m + 1)) z).symm
          rw [hφz, ← hb, ← hcomm', ha]
          exact sub_self _
        obtain ⟨β, hβ, _hφβ⟩ :=
          hkernel_succ m zγ hφγ
        apply
          cochainComplex_addCommGrp_homologyπ_eq_zero_of_preimage
            (K := K) m z (β + a)
        rw [map_add, hβ, hzγi]
        dsimp [γ]
        abel
  · intro y
    have hπsurj :
        Function.Surjective
          (ConcreteCategory.hom (L.homologyπ n)) :=
      (AddCommGrpCat.epi_iff_surjective (L.homologyπ n)).mp inferInstance
    obtain ⟨w, rfl⟩ := hπsurj y
    obtain ⟨a, ha⟩ := hsurj n (L.iCycles n w)
    let δ : K.X (n + 1) := K.d n (n + 1) a
    have hδclosed : K.d (n + 1) (n + 2) δ = 0 := by
      dsimp [δ]
      change
        (ConcreteCategory.hom
          (K.d n (n + 1) ≫ K.d (n + 1) (n + 2))) a = 0
      rw [K.d_comp_d]
      rfl
    have hnext :
        (ComplexShape.up ℕ).next (n + 1) = n + 2 :=
      (ComplexShape.up ℕ).next_eq'
        (by simp [ComplexShape.up_Rel])
    have hδclosedS : (K.sc (n + 1)).g δ = 0 := by
      change K.d (n + 1) ((ComplexShape.up ℕ).next (n + 1)) δ = 0
      rw [hnext]
      exact hδclosed
    let xδ : AddMonoidHom.ker (K.sc (n + 1)).g.hom :=
      ⟨δ, hδclosedS⟩
    let zδ : K.cycles (n + 1) :=
      (K.sc (n + 1)).abCyclesIso.inv xδ
    have hzδi : K.iCycles (n + 1) zδ = δ := by
      simpa [zδ, xδ] using
        ShortComplex.abCyclesIso_inv_apply_iCycles
          (K.sc (n + 1)) xδ
    have hφδ : φ.f (n + 1) (K.iCycles (n + 1) zδ) = 0 := by
      rw [hzδi]
      dsimp [δ]
      have hcomm :=
        ConcreteCategory.congr_hom (φ.comm n (n + 1)) a
      have hcomm' :
          L.d n (n + 1) (φ.f n a) =
            φ.f (n + 1) (K.d n (n + 1) a) := by
        change
          L.d n (n + 1) (φ.f n a) =
            φ.f (n + 1) (K.d n (n + 1) a) at hcomm
        exact hcomm
      calc
        φ.f (n + 1) (K.d n (n + 1) a) =
            L.d n (n + 1) (φ.f n a) := hcomm'.symm
        _ = L.d n (n + 1) (L.iCycles n w) := by rw [ha]
        _ = 0 := by
          change
            (ConcreteCategory.hom
              (L.iCycles n ≫ L.d n (n + 1))) w = 0
          rw [L.iCycles_d]
          rfl
    obtain ⟨β, hβ, hφβ⟩ :=
      hkernel_succ n zδ hφδ
    let c : K.X n := a - β
    have hcclosed : K.d n (n + 1) c = 0 := by
      dsimp [c]
      rw [map_sub, hβ, hzδi]
      dsimp [δ]
      exact sub_self _
    have hnextn : (ComplexShape.up ℕ).next n = n + 1 :=
      (ComplexShape.up ℕ).next_eq'
        (by simp [ComplexShape.up_Rel])
    have hcclosedS : (K.sc n).g c = 0 := by
      change K.d n ((ComplexShape.up ℕ).next n) c = 0
      rw [hnextn]
      exact hcclosed
    let xc : AddMonoidHom.ker (K.sc n).g.hom :=
      ⟨c, hcclosedS⟩
    let zc : K.cycles n :=
      (K.sc n).abCyclesIso.inv xc
    have hzci : K.iCycles n zc = c := by
      simpa [zc, xc] using
        ShortComplex.abCyclesIso_inv_apply_iCycles
          (K.sc n) xc
    refine ⟨K.homologyπ n zc, ?_⟩
    have hcycles : cyclesMap φ n zc = w := by
      apply
        (AddCommGrpCat.mono_iff_injective (L.iCycles n)).1
          inferInstance
      calc
        L.iCycles n (cyclesMap φ n zc) =
            φ.f n (K.iCycles n zc) := by
              exact
                ConcreteCategory.congr_hom
                  (cyclesMap_i φ n) zc
        _ = φ.f n c := by rw [hzci]
        _ = φ.f n a - φ.f n β := by
              exact map_sub _ _ _
        _ = L.iCycles n w := by rw [ha, hφβ, sub_zero]
    calc
      homologyMap φ n (K.homologyπ n zc) =
          L.homologyπ n (cyclesMap φ n zc) := by
            have hnat :=
              ConcreteCategory.congr_hom
                (homologyπ_naturality φ n) zc
            rw [ConcreteCategory.comp_apply,
              ConcreteCategory.comp_apply] at hnat
            exact hnat
      _ = L.homologyπ n w := by rw [hcycles]

/--
%%handwave
name:
  Subdivision identifies ordinary and sheafified singular-cochain cohomology
statement:
  Let $X$ be a paracompact Hausdorff space such that every open subspace is
  paracompact.  In every degree $n$, the map from ordinary real singular
  cochains on $X$ to global sections of the sheafified singular-cochain
  complex induces a bijection on cohomology.
proof:
  The comparison is degreewise surjective.  Its degree-zero kernel has no
  cycles, and every positive-degree kernel cocycle has a primitive remaining
  in the kernel, by the cover-small-chain subdivision equivalence.  Apply the
  general surjective-map criterion for an acyclic kernel.
-/
theorem
    openSingularCochainTopToSheafifiedGlobalSections_homologyMap_bijective_of_subdivision
    (X : TopCat.{v}) [T2Space X] [ParacompactSpace X]
    (hopen : ∀ V : Opens X, ParacompactSpace V)
    (_hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (n : ℕ) :
    Function.Bijective
      (ConcreteCategory.hom
        (HomologicalComplex.homologyMap
          (openSingularCochainTopToSheafifiedGlobalSections X) n)) := by
  let K :=
    (realSingularCochainOpenComplexFunctor X).obj
      (op (⊤ : Opens X))
  let L :=
    ((Sheaf.Γ (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
      (realSingularCochainSheafComplex X)
  let φ : K ⟶ L :=
    openSingularCochainTopToSheafifiedGlobalSections X
  apply
    cochainMap_homologyMap_bijective_of_surjective_kernel_acyclic
      φ
      (fun p =>
        openSingularCochainTopToSheafifiedGlobalSections_f_surjective
          X hopen p)
  · intro z hz
    have hη :=
      openSingularCochainTopToSheafifiedGlobalSections_toSheafify_eq_zero_of_f_eq_zero
        X 0 (K.iCycles 0 z) hz
    exact
      cochainComplex_addCommGrp_cycle_zero_of_homologyπ_zero_eq_zero
        (K := K) z
        (openSingularCochainTop_homologyπ_eq_zero_of_toSheafify_iCycles_eq_zero
          X 0 z hη)
  · intro m z hz
    have hη :=
      openSingularCochainTopToSheafifiedGlobalSections_toSheafify_eq_zero_of_f_eq_zero
        X (m + 1) (K.iCycles (m + 1) z) hz
    obtain ⟨β, hβ, hβη⟩ :=
      openSingularCochainTop_exists_kernel_primitive X m z hη
    exact
      ⟨β, hβ,
        openSingularCochainTopToSheafifiedGlobalSections_f_eq_zero_of_toSheafify_eq_zero
          X m β hβη⟩

/--
%%handwave
name:
  Real singular cohomology agrees with constant-sheaf cohomology, compatibly with scalars
statement:
  Let $X$ be a paracompact Hausdorff locally contractible space such that
  every open subspace of $X$ is paracompact.  For every $n$, there is an
  additive equivalence
  $H^n_{\mathrm{sing}}(X;\mathbb R)\cong
  H^n(X;\underline{\mathbb R})$ commuting with multiplication by every real
  scalar.
proof:
  Subdivision identifies ordinary singular-cochain cohomology with the
  cohomology of global sheafified singular cochains.  The latter computes
  constant-sheaf cohomology by the exact flasque singular-cochain resolution.
  Compose these equivalences with the canonical identification between the
  whole space and its terminal open subset.
-/
theorem
    exists_realSingularCohomology_addEquiv_realConstantSheafCohomology_with_smul_of_open_paracompact
    (X : TopCat.{v}) [T2Space X] [ParacompactSpace X]
    (hopen : ∀ V : Opens X, ParacompactSpace V)
    (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) :
    ∃ e :
        ↥(RealSingularCohomology X n) ≃+
          RealConstantSheafCohomology X n,
      ∀ (r : ℝ) (α : ↥(RealSingularCohomology X n)),
        e (r • α) = r • e α := by
  let K :=
    (realSingularCochainOpenComplexFunctor X).obj
      (op (⊤ : Opens X))
  let L :=
    ((Sheaf.Γ (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
      (realSingularCochainSheafComplex X)
  let φ := openSingularCochainTopToSheafifiedGlobalSections X
  let φH := HomologicalComplex.homologyMap φ n
  have hφH :
      Function.Bijective (ConcreteCategory.hom φH) :=
    openSingularCochainTopToSheafifiedGlobalSections_homologyMap_bijective_of_subdivision
      X hopen hloc n
  let eφ : ↥(K.homology n) ≃+ ↥(L.homology n) :=
    AddEquiv.ofBijective (ConcreteCategory.hom φH) hφH
  rcases
      realSingularCochainOpenComplexFunctor_top_homology_addEquiv_singularCohomology
        X n with
    ⟨eTop, hTop⟩
  rcases realSingularCohomology_topOpen_linearEquiv X n with
    ⟨eOpen⟩
  rcases
      exists_realSingularCochainSheafGlobalSectionsCohomology_addEquiv_realConstantSheafCohomology_with_map_smul_of_open_paracompact
        X hopen hloc n with
    ⟨eSheaf, hSheaf⟩
  let e :
      ↥(RealSingularCohomology X n) ≃+
        RealConstantSheafCohomology X n :=
    eOpen.symm.toAddEquiv.trans
      (eTop.symm.trans (eφ.trans eSheaf))
  refine ⟨e, ?_⟩
  intro r α
  let scalarTop :=
    HomologicalComplex.homologyMap
      ((realSingularCochainOpenComplexFunctorScalarNatTrans X r).app
        (op (⊤ : Opens X))) n
  let scalarSheaf :=
    HomologicalComplex.homologyMap
      (((Sheaf.Γ (Opens.grothendieckTopology X)
        AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
        (sheafifiedOpenRealSingularCochainSheafScalarEndConcrete X r)) n
  have hTopSymm (x :
      SingularCohomology ℝ ((Opens.toTopCat X).obj (⊤ : Opens X)) n) :
      eTop.symm (r • x) = scalarTop (eTop.symm x) := by
    apply eTop.injective
    calc
      eTop (eTop.symm (r • x)) = r • x := eTop.apply_symm_apply _
      _ = r • eTop (eTop.symm x) := by
        rw [eTop.apply_symm_apply]
      _ = eTop (scalarTop (eTop.symm x)) := by
        simpa [scalarTop] using (hTop r (eTop.symm x)).symm
  have hφScalar (x : ↥(K.homology n)) :
      eφ (scalarTop x) = scalarSheaf (eφ x) := by
    have hmaps :=
      openSingularCochainTopToSheafifiedGlobalSections_homology_scalar
        X r n
    have happ :=
      ConcreteCategory.congr_hom hmaps x
    simpa [eφ, φH, φ, scalarTop, scalarSheaf, K, L,
      ConcreteCategory.comp_apply] using happ.symm
  change
    eSheaf
        (eφ
          (eTop.symm
            (eOpen.symm (r • α)))) =
      r •
        eSheaf
          (eφ
            (eTop.symm
              (eOpen.symm α)))
  rw [eOpen.symm.map_smul, hTopSymm, hφScalar, hSheaf]

/--
%%handwave
name:
  Real singular cohomology is linearly equivalent to constant-sheaf cohomology
statement:
  Let $X$ be a paracompact Hausdorff locally contractible space such that
  every open subspace of $X$ is paracompact.  Then
  $H^n_{\mathrm{sing}}(X;\mathbb R)$ and
  $H^n(X;\underline{\mathbb R})$ are linearly equivalent over $\mathbb R$.
proof:
  Equip the scalar-compatible additive comparison between singular and
  constant-sheaf cohomology with its induced linear-equivalence structure.
tags:
  milestone
-/
theorem
    realSingularCohomology_nonempty_linearEquiv_realConstantSheafCohomology_of_open_paracompact
    (X : TopCat.{v}) [T2Space X] [ParacompactSpace X]
    (hopen : ∀ V : Opens X, ParacompactSpace V)
    (hloc : LocallyContractibleSpace X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    (n : ℕ) :
    Nonempty
      (↥(RealSingularCohomology X n) ≃ₗ[ℝ]
        RealConstantSheafCohomology X n) := by
  rcases
      exists_realSingularCohomology_addEquiv_realConstantSheafCohomology_with_smul_of_open_paracompact
        X hopen hloc n with
    ⟨e, he⟩
  exact
    ⟨{ toAddEquiv := e
       map_smul' := he }⟩












end ConstantSheaf

end

end Cohomology
end JJMath
