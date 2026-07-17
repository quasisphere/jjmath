import JJMath.Manifold.DeRhamComparison.Base

open scoped Manifold ContDiff Topology ZeroObject

namespace JJMath
namespace Manifold

open Set
open Topology
open Filter
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 80000

universe v w m uC vC tSmall tBig

variable {E : Type v} [NormedAddCommGroup E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]





/--
%%handwave
name:
  Sheafification in the smooth-form coefficient universe
statement:
  The open-set site of a topological space has sheafification for
  abelian-group-valued presheaves in the coefficient universe large enough for
  smooth differential forms.
proof:
  The open-cover categories are filtered and live in the space universe.  The
  forgetful functor from abelian groups preserves filtered colimits in the
  enlarged coefficient universe after shrinking the preservation universe, so
  the standard sheafification instance applies.
-/
theorem opens_addCommGrp_hasSheafify_smoothFormsUniverse (X : TopCat.{m}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m} := by
  classical
  haveI : PreservesFilteredColimitsOfSize.{m, m}
      (forget AddCommGrpCat.{max v m}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max v m})
  infer_instance

/--
%%handwave
name:
  Ext groups in the smooth-form coefficient universe
statement:
  The category of abelian-group sheaves on the open-set site has the Ext
  groups used for sheaf cohomology in the coefficient universe large enough
  for smooth differential forms.
proof:
  Once sheafification is available in that universe, abelian-group sheaves form
  an abelian category and, by passage to an essentially small open-set site, a
  Grothendieck abelian category in the same universe.  The general Ext
  construction for Grothendieck abelian categories then applies.
-/
theorem opens_addCommGrp_hasExt_smoothFormsUniverse (X : TopCat.{m})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}] :
    HasExt.{max v m}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}) := by
  letI : Abelian (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}) :=
    CategoryTheory.sheafIsAbelian
  letI : IsGrothendieckAbelian.{max v m}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}) :=
    CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall
      (Opens.grothendieckTopology X) AddCommGrpCat.{max v m}
  infer_instance












end

end Manifold
end JJMath
