import JJMath.Hyperbolic.Converse.Setup.Statements

/-!
# Lightweight bridge from the complete converse target to the public endpoint

This module contains endpoint consequences that follow directly from
`CompletePartialConverseTheorem`.
-/

namespace JJMath

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/-- The complete partial converse gives a complex projective structure induced by `g`.

%%handwave
name:
  The complete converse specializes to a fixed hyperbolic metric
statement:
  Suppose every hyperbolic metric on a Riemann surface $X$ induces a complex
  projective structure with holonomy in $\mathrm{PSL}_2(\mathbb R)$. Then for
  a fixed hyperbolic metric $g$, there exist an induced projective structure
  $P$ and a basepoint $x_0$ for which the holonomy lies in
  $\mathrm{PSL}_2(\mathbb R)$.
proof:
  Evaluate the assumed universal statement at the metric $g$.
-/
theorem exists_complex_projective_structure_induced_by_metric_of_complete_partial_converse_theorem
    (h : CompletePartialConverseTheorem X) (g : HyperbolicMetric X) :
    ∃ P : ComplexProjectiveStructure X,
      P.IsInducedByHyperbolicMetric g ∧
        ∃ x₀ : X, HasPSL2RHolonomy x₀ P :=
  h g

end HyperbolicMetric

end JJMath
