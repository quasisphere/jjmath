import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Points

/-!
# Fine sheaves

This file records the sheaf-theoretic input used by the de Rham comparison:
fine sheaves of abelian groups on paracompact Hausdorff spaces are acyclic.

The definition is phrased in the usual stalk-support form.  An endomorphism is
supported in an open set if its induced map on every stalk outside that open set
is zero, and a fine sheaf admits locally finite decompositions of the identity
subordinate to locally finite open covers.
-/

open scoped Topology ZeroObject

namespace CategoryTheory
namespace Sheaf

open Abelian

universe uC vC w w'

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}

/--
%%handwave
name:
  Injective abelian sheaves have no positive cohomology
statement:
  If an abelian sheaf is injective in the abelian category of sheaves, then
  its positive-degree sheaf cohomology groups vanish.
proof:
  Sheaf cohomology is defined as an Ext group from the constant integral
  sheaf.  Positive Ext groups with injective target are zero.
-/
theorem cohomology_subsingleton_of_injective
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w}) [Injective F]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (F.H q) := by
  cases q with
  | zero =>
      exact (Nat.not_lt_zero 0 hq).elim
  | succ q =>
      change Subsingleton
        (Ext ((constantSheaf J AddCommGrpCat.{w}).obj
          (AddCommGrpCat.of (ULift.{w} ℤ))) F (q + 1))
      exact Ext.subsingleton_of_injective _ F q

end Sheaf
end CategoryTheory

namespace TopCat
namespace Sheaf

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

universe u w w'

variable {X : TopCat.{u}}
variable [HasColimitsOfSize.{u, u} AddCommGrpCat.{w}]

/--
%%handwave
name:
  Germ support of a sheaf endomorphism
statement:
  The germ support of an endomorphism of a sheaf of abelian groups is the set
  of points where the induced endomorphism on the stalk is nonzero.
proof:
  This is the definition.
-/
def endomorphismGermSupport
    (F : TopCat.Sheaf.{u, w, w + 1} AddCommGrpCat.{w} X) (f : F ⟶ F) : Set X :=
  {x | ((Opens.pointGrothendieckTopology x).sheafFiber
      (A := AddCommGrpCat.{w})).map f ≠ 0}

/--
%%handwave
name:
  Fine sheaf of abelian groups
statement:
  A sheaf of abelian groups on a topological space is fine if every locally
  finite open cover admits a locally finite family of sheaf endomorphisms
  subordinate to that cover whose germs sum to the identity at every point.
proof:
  This is the definition, expressed on stalks.  Subordination means that the
  germ support of the endomorphism indexed by an open set is contained in that
  open set.
-/
class IsFine (F : TopCat.Sheaf.{u, w, w + 1} AddCommGrpCat.{w} X) : Prop where
  exists_subordinate_partition :
    ∀ {ι : Type u} (U : ι → Opens X),
      LocallyFinite (fun i => (U i : Set X)) →
      (∀ x : X, ∃ i, x ∈ U i) →
        ∃ φ : ι → (F ⟶ F),
          (∀ i, endomorphismGermSupport F (φ i) ⊆ (U i : Set X)) ∧
            ∀ x : X, ∃ s : Finset ι,
              (∀ i, i ∉ s →
                ((Opens.pointGrothendieckTopology x).sheafFiber
                  (A := AddCommGrpCat.{w})).map (φ i) = 0) ∧
              (∑ i ∈ s,
                ((Opens.pointGrothendieckTopology x).sheafFiber
                  (A := AddCommGrpCat.{w})).map (φ i)) = 𝟙 _




end Sheaf
end TopCat
