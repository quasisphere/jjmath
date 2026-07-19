import JJMath.Hyperbolic.Converse.EndpointBridge
import JJMath.Hyperbolic.Converse.SelectedContinuation.CoreRoute

/-!
# Public endpoint for the hyperbolic-to-projective converse

This module is the small public landing point for the completed partial
converse.  The proof is provided by the selected-continuation route; importing
this module exposes the unconditional theorem in its unbased form.
-/

namespace JJMath

namespace HyperbolicMetric

/-- A hyperbolic metric has a complex projective structure induced by it.

%%handwave
name:
  A hyperbolic metric induces a complex projective structure
statement:
  For every hyperbolic metric $g$ on a Riemann surface $X$, there exists a
  complex projective structure $P$ on $X$ whose projective developing map is
  obtained by projectivizing a developing map for $g$.
proof:
  Apply [there is an induced complex projective structure with real projective holonomy](lean:JJMath.HyperbolicMetric.exists_complex_projective_structure_induced_by_metric_of_complete_partial_converse_theorem) to the completed converse theorem, then retain only the induced projective structure.
-/
theorem exists_complex_projective_structure_induced_by_metric
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (g : HyperbolicMetric X) :
    ∃ P : ComplexProjectiveStructure X,
      P.IsInducedByHyperbolicMetric g :=
  let h :=
    exists_complex_projective_structure_induced_by_metric_of_complete_partial_converse_theorem
      complete_partial_converse_theorem g
  by
    rcases h with ⟨P, hPg, _hPSL⟩
    exact ⟨P, hPg⟩

/--
A hyperbolic metric has a complex projective structure induced by it, with
`PSL(2, ℝ)` holonomy.

%%handwave
name:
  A hyperbolic metric induces a projective structure with real holonomy
statement:
  For every hyperbolic metric $g$ on a Riemann surface $X$, there exist a
  complex projective structure $P$ induced by $g$ and a basepoint $x_0\in X$
  such that the holonomy of $P$ is the complexification of a representation
  $\pi_1(X,x_0)\to\mathrm{PSL}_2(\mathbb R)$.
proof:
  Apply [the completed converse produces an induced projective structure together with real projective holonomy](lean:JJMath.HyperbolicMetric.exists_complex_projective_structure_induced_by_metric_of_complete_partial_converse_theorem) to the formal partial-converse theorem.
-/
theorem exists_complex_projective_structure_induced_by_metric_with_psl2r_holonomy
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (g : HyperbolicMetric X) :
    ∃ P : ComplexProjectiveStructure X,
      P.IsInducedByHyperbolicMetric g ∧
        ∃ x₀ : X, HasPSL2RHolonomy x₀ P :=
  exists_complex_projective_structure_induced_by_metric_of_complete_partial_converse_theorem
    complete_partial_converse_theorem g

end HyperbolicMetric

end JJMath
