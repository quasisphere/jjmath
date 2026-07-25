import JJMath.Manifold.CirclePrimitive
import JJMath.Uniformization.ExteriorAngularExtension

/-!
# An alternative circle primitive of the annular angular form

The annular angular representative is obtained from Mayer--Vietoris by
differentiating two local zero-forms.  Their difference on the two components
of the overlap is respectively one and zero.  After multiplication by
`2 * pi`, their complex exponentials therefore agree and glue to a global
circle-valued primitive.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Uniformization

open JJMath.Manifold

noncomputable section

end
end Uniformization
end JJMath
