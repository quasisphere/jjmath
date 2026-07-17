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

/-- A hyperbolic metric has a complex projective structure induced by it. -/
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
