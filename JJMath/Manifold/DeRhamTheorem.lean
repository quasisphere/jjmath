import JJMath.Manifold.DeRhamComparison.Final

/-!
# De Rham theorem

This file contains the comparison layer between real de Rham cohomology and
real singular cohomology.  It is kept separate from `JJMath.Manifold.DeRham`
so that the basic de Rham complex and Mayer-Vietoris API do not have to import
the singular cohomology development.
-/

open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

universe v w m

variable {E : Type v} [NormedAddCommGroup E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]













end

end Manifold
end JJMath
