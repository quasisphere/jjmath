import JJMath.ComplexProjective.Holonomy
import JJMath.Hyperbolic.DevelopingMap

/-!
# Real projective structures and singular hyperbolic metrics

This file records the relationship between complex projective structures with
real holonomy and the hyperbolic metrics induced by their developing maps.
-/

namespace JJMath

open scoped MatrixGroups

namespace HolonomyRepresentation

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/--
A complex projective holonomy representation is literally induced from a real
Mobius holonomy representation by complexification.
-/
def IsComplexificationOfReal (χ : HolonomyRepresentation X x₀) : Prop :=
  ∃ ρ : RealHolonomyRepresentation X x₀,
    χ.toMonoidHom = realMobiusToMobiusGroup.comp ρ.toMonoidHom

end HolonomyRepresentation

/--
A Mobius postcomposition that conjugates a complex projective holonomy
representation into the complexified real Mobius group.

If a projective developing map has holonomy `χ` and we replace it by
`A ∘ dev`, the new holonomy is `A * χ * A⁻¹`.  This package records that the
new holonomy is the image of a `PSL(2, ℝ)` representation.
-/
structure ProjectiveHolonomyMobiusNormalization
    {X : Type} [TopologicalSpace X] (x₀ : X)
    (χ : HolonomyRepresentation X x₀) where
  /-- The Mobius transformation used to postcompose the projective developing map. -/
  postcomposition : MobiusRepresentative
  /-- The resulting real holonomy representation. -/
  realHolonomy : RealHolonomyRepresentation X x₀
  /--
  After postcomposition, the conjugated complex holonomy is the complexification
  of the real holonomy.
  -/
  normalized_holonomy_eq :
    ∀ γ,
      Matrix.ProjGenLinGroup.mk postcomposition * χ γ *
          (Matrix.ProjGenLinGroup.mk postcomposition)⁻¹ =
        realMobiusToMobiusGroup (realHolonomy γ)

namespace HolonomyRepresentation

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/--
A complex projective holonomy representation is conjugate into `PSL(2, ℝ)` if
some Mobius postcomposition normalizes it to a complexification of real
holonomy.
-/
def IsConjugateIntoPSL2R (χ : HolonomyRepresentation X x₀) : Prop :=
  Nonempty (ProjectiveHolonomyMobiusNormalization x₀ χ)

end HolonomyRepresentation

namespace ProjectiveHolonomyMobiusNormalization

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- The projective class of the normalizing Mobius transformation. -/
def postcompositionClass {χ : HolonomyRepresentation X x₀}
    (N : ProjectiveHolonomyMobiusNormalization x₀ χ) : MobiusGroup :=
  Matrix.ProjGenLinGroup.mk N.postcomposition

/-- The pointwise normalized projective holonomy representation. -/
noncomputable def normalizedHolonomy {χ : HolonomyRepresentation X x₀}
    (N : ProjectiveHolonomyMobiusNormalization x₀ χ)
    (γ : FundamentalGroup X x₀) : MobiusGroup :=
  N.postcompositionClass * χ γ * (N.postcompositionClass)⁻¹

@[simp]
theorem normalizedHolonomy_eq_real {χ : HolonomyRepresentation X x₀}
    (N : ProjectiveHolonomyMobiusNormalization x₀ χ)
    (γ : FundamentalGroup X x₀) :
    N.normalizedHolonomy γ = realMobiusToMobiusGroup (N.realHolonomy γ) :=
  N.normalized_holonomy_eq γ

/--
The holonomy representation obtained after postcomposing projective coordinates
by the normalizing Mobius transformation.
-/
noncomputable def normalizedHolonomyRepresentation
    {χ : HolonomyRepresentation X x₀}
    (N : ProjectiveHolonomyMobiusNormalization x₀ χ) :
    HolonomyRepresentation X x₀ where
  toMonoidHom :=
    { toFun := N.normalizedHolonomy
      map_one' := by
        simp [normalizedHolonomy]
      map_mul' := by
        intro γ δ
        simp [normalizedHolonomy, mul_assoc] }

/--
The normalized projective holonomy representation is the complexification of
the real holonomy recorded by the normalization.
-/
theorem normalizedHolonomyRepresentation_complexifies_real
    {χ : HolonomyRepresentation X x₀}
    (N : ProjectiveHolonomyMobiusNormalization x₀ χ) :
    N.normalizedHolonomyRepresentation.toMonoidHom =
      realMobiusToMobiusGroup.comp N.realHolonomy.toMonoidHom := by
  ext γ
  exact N.normalizedHolonomy_eq_real γ

/--
After Mobius postcomposition, the normalized complex projective holonomy is a
literal complexification of real holonomy.
-/
theorem normalizedHolonomyRepresentation_isComplexificationOfReal
    {χ : HolonomyRepresentation X x₀}
    (N : ProjectiveHolonomyMobiusNormalization x₀ χ) :
    N.normalizedHolonomyRepresentation.IsComplexificationOfReal :=
  ⟨N.realHolonomy, N.normalizedHolonomyRepresentation_complexifies_real⟩

/-- The normalized representation evaluates to the conjugated holonomy. -/
@[simp]
theorem normalizedHolonomyRepresentation_apply
    {χ : HolonomyRepresentation X x₀}
    (N : ProjectiveHolonomyMobiusNormalization x₀ χ)
    (γ : FundamentalGroup X x₀) :
    N.normalizedHolonomyRepresentation γ = N.normalizedHolonomy γ :=
  rfl

/--
If the original projective holonomy is already the complexification of real
holonomy, the identity postcomposition is a normalization.
-/
def of_complexified_real
    (ρ : RealHolonomyRepresentation X x₀) (χ : HolonomyRepresentation X x₀)
    (hχ : χ.toMonoidHom = realMobiusToMobiusGroup.comp ρ.toMonoidHom) :
    ProjectiveHolonomyMobiusNormalization x₀ χ where
  postcomposition := 1
  realHolonomy := ρ
  normalized_holonomy_eq := by
    intro γ
    rw [hχ]
    simp

/--
Literal complexification is the special case of conjugacy into `PSL(2, ℝ)`
with identity Mobius postcomposition.
-/
theorem isConjugateIntoPSL2R_of_isComplexificationOfReal
    {χ : HolonomyRepresentation X x₀}
    (hχ : χ.IsComplexificationOfReal) :
    χ.IsConjugateIntoPSL2R := by
  rcases hχ with ⟨ρ, hρ⟩
  exact ⟨ProjectiveHolonomyMobiusNormalization.of_complexified_real ρ χ hρ⟩

end ProjectiveHolonomyMobiusNormalization

namespace HolonomyRepresentation

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- Choose a Mobius normalization from a proof that holonomy is conjugate into `PSL(2, ℝ)`. -/
noncomputable def mobiusNormalization {χ : HolonomyRepresentation X x₀}
    (hχ : χ.IsConjugateIntoPSL2R) :
    ProjectiveHolonomyMobiusNormalization x₀ χ :=
  Classical.choice hχ

/--
The holonomy representation obtained after applying the chosen Mobius
normalization.
-/
noncomputable def normalizedRepresentationOfConjugateIntoPSL2R
    {χ : HolonomyRepresentation X x₀} (hχ : χ.IsConjugateIntoPSL2R) :
    HolonomyRepresentation X x₀ :=
  (χ.mobiusNormalization hχ).normalizedHolonomyRepresentation

/--
The chosen normalized representation associated to a conjugacy-into-`PSL(2, ℝ)`
witness is a literal complexification of real holonomy.
-/
theorem normalizedRepresentationOfConjugateIntoPSL2R_isComplexificationOfReal
    {χ : HolonomyRepresentation X x₀} (hχ : χ.IsConjugateIntoPSL2R) :
    (χ.normalizedRepresentationOfConjugateIntoPSL2R hχ).IsComplexificationOfReal :=
  (χ.mobiusNormalization hχ).normalizedHolonomyRepresentation_isComplexificationOfReal

end HolonomyRepresentation

/--
A concrete unlifted real-holonomy certificate for a based complex projective
structure.

The important point is that the holonomy representation is not floating freely:
it is accompanied by the atlas data saying that it is the holonomy constructed
from this particular projective structure.
-/
structure ComplexProjectiveStructure.RealHolonomyData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) (P : ComplexProjectiveStructure X) where
  /-- The complex projective holonomy read from the projective atlas. -/
  projectiveHolonomy : HolonomyRepresentation X x₀
  /-- Concrete atlas data tying the holonomy to `P`. -/
  holonomy_constructed_from_projective_charts :
    ProjectiveHolonomyConstructionData X x₀ P projectiveHolonomy
  /-- The underlying real holonomy representation. -/
  realHolonomy : RealHolonomyRepresentation X x₀
  /-- The projective holonomy is the complexification of the real holonomy. -/
  projectiveHolonomy_eq_real :
    projectiveHolonomy.toMonoidHom = realMobiusToMobiusGroup.comp realHolonomy.toMonoidHom

namespace ComplexProjectiveStructure.RealHolonomyData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {P : ComplexProjectiveStructure X}

/-- The stored projective holonomy is a literal complexification of real holonomy. -/
theorem projectiveHolonomy_isComplexificationOfReal
    (H : P.RealHolonomyData x₀) :
    H.projectiveHolonomy.IsComplexificationOfReal :=
  ⟨H.realHolonomy, H.projectiveHolonomy_eq_real⟩

/-- Real holonomy gives the identity Mobius normalization into `PSL(2, ℝ)`. -/
def mobiusPostcompositionData
    (H : P.RealHolonomyData x₀) :
    ProjectiveHolonomyMobiusNormalization x₀ H.projectiveHolonomy :=
  ProjectiveHolonomyMobiusNormalization.of_complexified_real
    H.realHolonomy H.projectiveHolonomy H.projectiveHolonomy_eq_real

end ComplexProjectiveStructure.RealHolonomyData

/--
A stronger certificate that the real holonomy of a projective structure has a
chosen `SL(2, ℝ)` lift.

This is deliberately separate from `RealHolonomyData`: PSL-valued holonomy is
the mathematical conclusion, while liftability is extra structure used by the
current hyperbolic developing-map construction when it is available.
-/
structure ComplexProjectiveStructure.LiftedRealHolonomyData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) (P : ComplexProjectiveStructure X)
    extends P.RealHolonomyData x₀ where
  /-- A chosen lift of the real holonomy to `SL(2, ℝ)`. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- The unlifted real holonomy is induced by the chosen lift. -/
  realHolonomy_is_lifted :
    toRealHolonomyData.realHolonomy.IsInducedByLift holonomyLift

/--
A concrete certificate that a based projective structure becomes real after a
Mobius postcomposition.
-/
structure ComplexProjectiveStructure.RealHolonomyAfterMobiusPostcompositionData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) (P : ComplexProjectiveStructure X) where
  /-- The complex projective holonomy read from the projective atlas. -/
  projectiveHolonomy : HolonomyRepresentation X x₀
  /-- Concrete atlas data tying the holonomy to `P`. -/
  holonomy_constructed_from_projective_charts :
    ProjectiveHolonomyConstructionData X x₀ P projectiveHolonomy
  /-- The Mobius normalization carrying the holonomy into the real subgroup. -/
  normalization : ProjectiveHolonomyMobiusNormalization x₀ projectiveHolonomy

/--
A complex projective structure has real holonomy if the holonomy constructed
from its own projective atlas is the complexification of a real representation.
-/
def HasPSL2RHolonomy {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  Nonempty (P.RealHolonomyData x₀)

/-- A projective structure with coordinate changes in the complexified `PSL(2, ℝ)` subgroup. -/
abbrev PSL2RProjectiveStructure (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] : Type :=
  ProjectiveStructureWithGroup psl2rMobiusSubgroup X

/--
A complex projective structure has lifted real holonomy if its PSL-valued
holonomy certificate comes with a chosen `SL(2, ℝ)` lift.
-/
def HasLiftedPSL2RHolonomy {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  Nonempty (P.LiftedRealHolonomyData x₀)

/-- Lifted real holonomy implies the unlifted `PSL(2, ℝ)` holonomy property. -/
theorem hasPSL2RHolonomy_of_hasLiftedPSL2RHolonomy
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : HasLiftedPSL2RHolonomy x₀ P) :
    HasPSL2RHolonomy x₀ P := by
  rcases h with ⟨H⟩
  exact ⟨H.toRealHolonomyData⟩

/--
A projective structure has holonomy conjugate into `PSL(2, ℝ)` if one can
postcompose its projective developing coordinates by a Mobius transformation so
that the conjugated holonomy factors through `PSL(2, ℝ)`.

The witness is tied to the projective structure by concrete holonomy
construction data for the same atlas.
-/
def HasPSL2RHolonomyAfterMobiusPostcomposition
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  Nonempty (P.RealHolonomyAfterMobiusPostcompositionData x₀)

/--
The non-conjugated real-holonomy package is the special case with identity
Mobius postcomposition.
-/
theorem hasPSL2RHolonomyAfterMobiusPostcomposition_of_hasPSL2RHolonomy
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {P : ComplexProjectiveStructure X}
    (h : HasPSL2RHolonomy x₀ P) :
    HasPSL2RHolonomyAfterMobiusPostcomposition x₀ P := by
  rcases h with ⟨H⟩
  exact ⟨{
    projectiveHolonomy := H.projectiveHolonomy
    holonomy_constructed_from_projective_charts :=
      H.holonomy_constructed_from_projective_charts
    normalization := H.mobiusPostcompositionData
  }⟩

end JJMath
