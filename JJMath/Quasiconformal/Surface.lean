import JJMath.ComplexProjective.Prerequisites.RiemannSurface
import JJMath.ComplexProjective.PQDifferential
import JJMath.Quasiconformal.ChangeOfVariables

/-!
# Quasiregular and quasiconformal maps between Riemann surfaces

The public predicates in this file are chartwise but do not mention a
particular atlas in their interface.  Coordinate representations are formed
from the complex charts selected at source and target points.  For continuous
maps, bounded distortion is required on every maximal chart-overlap domain.
For homeomorphisms, these representations are open partial homeomorphisms, so
the planar quasiconformal predicate applies directly.
-/

namespace JJMath

open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [RiemannSurface Y]

namespace Quasiconformal

/--
%%handwave
name:
  Source domain of a coordinate representation between Riemann surfaces
statement:
  Let $f:X\to Y$ be a map between Riemann surfaces, and choose complex
  charts $\phi_x$ at $x\in X$ and $\psi_y$ at $y\in Y$. The maximal source
  of the corresponding coordinate map is
  $$
    U_{x,y}(f)=
      \{z\in\phi_x(X):f(\phi_x^{-1}(z))\in\operatorname{source}(\psi_y)\}.
  $$
-/
def riemannSurfaceChartMapSource
    (f : X → Y) (x : X) (y : Y) : Set ℂ :=
  {z | z ∈ (chartAt ℂ x).target ∧
    f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ y).source}

/--
%%handwave
name:
  Coordinate representation of a map between Riemann surfaces
statement:
  For a map $f:X\to Y$ and complex charts $\phi_x,\psi_y$ at
  $x\in X,y\in Y$, its coordinate representation is
  $$
    f_{x,y}(z)=\psi_y\bigl(f(\phi_x^{-1}(z))\bigr).
  $$
  It is used on the maximal source $U_{x,y}(f)$ where both chart evaluations
  are valid.
-/
def riemannSurfaceChartMap
    (f : X → Y) (x : X) (y : Y) : ℂ → ℂ :=
  fun z ↦ chartAt ℂ y (f ((chartAt ℂ x).symm z))

end Quasiconformal

namespace BeltramiDifferential

open Quasiconformal

/--
%%handwave
name:
  Realization of a Beltrami differential by a surface homeomorphism
statement:
  Let $F:X\to Y$ be a homeomorphism of Riemann surfaces and let
  $\mu$ be a Beltrami differential on $X$. The map $F$ realizes
  $\mu$ when, in local complex coordinates $z$ about every $x\in X$
  and $w$ about $F(x)$, the coordinate map
  $w\circ F\circ z^{-1}$ belongs to $W^{1,2}_{\mathrm{loc}}$ and has a
  weak differential satisfying
  $$
    \partial_{\overline z}(w\circ F\circ z^{-1})
      =\mu_z\,\partial_z(w\circ F\circ z^{-1})
  $$
  almost everywhere on its coordinate domain.
-/
def IsBeltramiDifferentialOf
    (μ : BeltramiDifferential X) (F : X ≃ₜ Y) : Prop :=
  ∀ x : X,
    ∃ dF : ℂ → ℂ →L[ℝ] ℂ,
      IsLocalW12On
          (riemannSurfaceChartMapSource F x (F x))
          (riemannSurfaceChartMap F x (F x)) dF ∧
        WeakBeltramiEquationOn
          (riemannSurfaceChartMapSource F x (F x))
          (PQDifferential.inChart μ (achart ℂ x)) dF

end BeltramiDifferential

namespace Quasiconformal

/--
%%handwave
name:
  Coordinate partial homeomorphism of a surface homeomorphism
statement:
  If $F:X\to Y$ is a homeomorphism of Riemann surfaces and
  $\phi_x,\psi_y$ are complex charts, its maximal coordinate
  partial homeomorphism is
  $$
    \psi_y\circ F\circ\phi_x^{-1}.
  $$
-/
def riemannSurfaceChartRepresentation
    (F : X ≃ₜ Y) (x : X) (y : Y) :
    OpenPartialHomeomorph ℂ ℂ :=
  (chartAt ℂ x).symm.trans
    (F.toOpenPartialHomeomorph.trans (chartAt ℂ y))

/--
%%handwave
name:
  Coordinate homeomorphism of a surface homeomorphism
statement:
  The coordinate partial homeomorphism
  $\psi_y\circ F\circ\phi_x^{-1}$ restricts to a homeomorphism between its
  maximal open source and target domains in $\mathbb C$.
-/
def riemannSurfaceChartHomeomorph
    (F : X ≃ₜ Y) (x : X) (y : Y) :
    (riemannSurfaceChartRepresentation F x y).source ≃ₜ
      (riemannSurfaceChartRepresentation F x y).target :=
  (riemannSurfaceChartRepresentation F x y).toHomeomorphSourceTarget

/--
%%handwave
name:
  Quantitative quasiconformality between Riemann surfaces
statement:
  A homeomorphism $F:X\to Y$ between Riemann surfaces is
  $K$-quasiconformal if $K\geq1$ and every complex-coordinate
  representation
  $$
    \psi_y\circ F\circ\phi_x^{-1}
  $$
  is a planar $K$-quasiconformal homeomorphism on its maximal source domain.
-/
def IsKQuasiconformalBetweenRiemannSurfaces
    (K : ℝ) (F : X ≃ₜ Y) : Prop :=
  1 ≤ K ∧
    ∀ x : X, ∀ y : Y,
      IsKQuasiconformalBetween K
        (riemannSurfaceChartHomeomorph F x y)

/--
%%handwave
name:
  Source of the coordinate representation of a surface homeomorphism
statement:
  For a surface homeomorphism $F:X\to Y$, the source of the coordinate
  partial homeomorphism $\psi_y\circ F\circ\phi_x^{-1}$ is exactly
  $U_{x,y}(F)$, the maximal source of the corresponding coordinate map.
proof:
  Expand the source of both partial-homeomorphism compositions. The middle
  homeomorphism is defined on all of $X$.
-/
theorem riemannSurfaceChartRepresentation_source
    (F : X ≃ₜ Y) (x : X) (y : Y) :
    (riemannSurfaceChartRepresentation F x y).source =
      riemannSurfaceChartMapSource F x y := by
  ext z
  simp [riemannSurfaceChartRepresentation, riemannSurfaceChartMapSource]

end Quasiconformal

end

end JJMath
