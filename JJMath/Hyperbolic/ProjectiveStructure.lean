import JJMath.Hyperbolic.Pipeline
import JJMath.Hyperbolic.RealProjective

/-!
# Projective structures induced by hyperbolic metrics

A hyperbolic developing map `dev : X̃ → ℍ` is also a projective developing map
after composing with the inclusion `ℍ ⊂ ℂP¹`.  Its real Mobius holonomy then
gives a complex projective structure whose holonomy is conjugate into
`PSL(2, ℝ)`.

This file records the output package and theorem targets for that construction.
The actual construction of the projective atlas from local inverse branches of
the developing map is supplied by the converse assembly theorem inputs.
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

/-- The inclusion of the upper half-plane into the Riemann sphere. -/
def upperHalfPlaneToRiemannSphere (z : ℍ) : RiemannSphere :=
  ((z : ℂ) : RiemannSphere)

@[simp]
theorem upperHalfPlaneToRiemannSphere_apply (z : ℍ) :
    upperHalfPlaneToRiemannSphere z = ((z : ℂ) : RiemannSphere) :=
  rfl

/--
%%handwave
name:
  Equivariance of the inclusion $\mathbb H\hookrightarrow\mathbb{CP}^1$
statement:
  Let $A\in\mathrm{SL}_2(\mathbb R)$ and $z\in\mathbb H$. If
  $\iota:\mathbb H\hookrightarrow\mathbb{CP}^1$ is the standard inclusion and
  $A_{\mathbb C}$ is obtained from $A$ by extending scalars, then
  $\iota(A\cdot z)=A_{\mathbb C}\cdot\iota(z)$.
proof:
  Writing $A=\begin{psmallmatrix}a&b\\c&d\end{psmallmatrix}$, the denominator
  $cz+d$ is nonzero for $z\in\mathbb H$. Both sides are therefore the finite
  projective point represented by $(az+b)/(cz+d)$.
-/
theorem realMobiusRepresentative_projective_action
    (A : RealMobiusRepresentative) (z : ℍ) :
    upperHalfPlaneToRiemannSphere (realMobiusRepresentativeAction A z) =
      realMobiusRepresentativeAsMobiusRepresentative A •
        upperHalfPlaneToRiemannSphere z := by
  rw [upperHalfPlaneToRiemannSphere_apply, upperHalfPlaneToRiemannSphere_apply]
  rw [OnePoint.smul_some_eq_ite]
  have hden : ¬ ((realMobiusRepresentativeAsMobiusRepresentative A) 1 0 : ℂ) *
      (z : ℂ) + ((realMobiusRepresentativeAsMobiusRepresentative A) 1 1 : ℂ) = 0 := by
    simpa [realMobiusRepresentativeAsMobiusRepresentative, UpperHalfPlane.denom]
      using UpperHalfPlane.denom_ne_zero ((A : GL (Fin 2) ℝ)) z
  rw [if_neg hden]
  simp [realMobiusRepresentativeAction, realMobiusRepresentativeAsMobiusRepresentative,
    UpperHalfPlane.coe_specialLinearGroup_apply]

namespace HyperbolicDevelopingMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- The projective developing map obtained by composing `dev : X̃ → ℍ` with `ℍ ⊂ ℂP¹`. -/
def projectiveDev (D : HyperbolicDevelopingMap X x₀ g) :
    D.cover.total → RiemannSphere :=
  fun y ↦ upperHalfPlaneToRiemannSphere (D.dev y)

/-- The complex projective holonomy obtained by complexifying real hyperbolic holonomy. -/
def projectiveHolonomy (D : HyperbolicDevelopingMap X x₀ g) :
    HolonomyRepresentation X x₀ where
  toMonoidHom := realMobiusToMobiusGroup.comp D.holonomy.toMonoidHom

/-- A projective holonomy representation is the complexification of real hyperbolic holonomy. -/
def ProjectiveHolonomyComplexifiesReal (D : HyperbolicDevelopingMap X x₀ g)
    (ρ : HolonomyRepresentation X x₀) : Prop :=
  ρ.toMonoidHom = realMobiusToMobiusGroup.comp D.holonomy.toMonoidHom

/--
Projective equivariance of the composed developing map, stated with explicit
`GL(2, ℂ)` representatives of projective holonomy.

This avoids needing a global `PGL(2, ℂ)` action on the Riemann sphere: for each
loop, a representative of the projective holonomy sends the projective
coordinate of every `y` to that of its deck translate.
-/
def ProjectiveEquivariant (D : HyperbolicDevelopingMap X x₀ g)
    (ρ : HolonomyRepresentation X x₀) : Prop :=
  ∀ γ, ∃ A : MobiusRepresentative,
    Matrix.ProjGenLinGroup.mk A = ρ γ ∧
      ∀ y, D.projectiveDev (D.cover.deckAction γ y) = A • D.projectiveDev y

@[simp]
theorem projectiveHolonomy_complexifies_real (D : HyperbolicDevelopingMap X x₀ g) :
    D.ProjectiveHolonomyComplexifiesReal D.projectiveHolonomy :=
  rfl

@[simp]
theorem projectiveDev_apply (D : HyperbolicDevelopingMap X x₀ g)
    (y : D.cover.total) :
    D.projectiveDev y = upperHalfPlaneToRiemannSphere (D.dev y) :=
  rfl

/--
%%handwave
name:
  Projectivization preserves equivariance
statement:
  Let $\operatorname{dev}:\widetilde X_{x_0}\to\mathbb H$ be equivariant for
  $\rho:\pi_1(X,x_0)\to\mathrm{PSL}_2(\mathbb R)$. Then
  $\iota\circ\operatorname{dev}:\widetilde X_{x_0}\to\mathbb{CP}^1$ is
  equivariant for the complexified representation
  $\iota_*\rho:\pi_1(X,x_0)\to\mathrm{PGL}_2(\mathbb C)$.
proof:
  For each $\gamma\in\pi_1(X,x_0)$, choose $A_\gamma\in\mathrm{SL}_2(\mathbb R)$ representing $\rho(\gamma)$ and complexify it. [The inclusion $\mathbb H\hookrightarrow\mathbb{CP}^1$ intertwines the real Möbius action with its complexification](lean:JJMath.realMobiusRepresentative_projective_action), so $\iota(\operatorname{dev}(\gamma y))=A_{\gamma,\mathbb C}\cdot\iota(\operatorname{dev}(y))$ for every $y\in\widetilde X_{x_0}$.
-/
theorem projectiveEquivariant
    (D : HyperbolicDevelopingMap X x₀ g) :
    D.ProjectiveEquivariant D.projectiveHolonomy := by
  intro γ
  rcases QuotientGroup.mk'_surjective
      (Subgroup.center RealMobiusRepresentative) (D.holonomy γ) with
    ⟨A, hA⟩
  refine ⟨realMobiusRepresentativeAsMobiusRepresentative A, ?_, ?_⟩
  · change
      Matrix.ProjGenLinGroup.mk (realMobiusRepresentativeAsMobiusRepresentative A) =
        realMobiusToMobiusGroup (D.holonomy γ)
    rw [← hA]
    rfl
  · intro y
    change
      upperHalfPlaneToRiemannSphere
          (D.dev (D.cover.deckAction γ y)) =
        realMobiusRepresentativeAsMobiusRepresentative A •
          upperHalfPlaneToRiemannSphere (D.dev y)
    rw [D.equivariant γ y]
    change
      upperHalfPlaneToRiemannSphere
          (realMobiusAction (D.holonomy γ) (D.dev y)) =
        realMobiusRepresentativeAsMobiusRepresentative A •
          upperHalfPlaneToRiemannSphere (D.dev y)
    rw [← hA]
    change
      upperHalfPlaneToRiemannSphere
          (realMobiusAction (realMobiusProjection A) (D.dev y)) =
        realMobiusRepresentativeAsMobiusRepresentative A •
          upperHalfPlaneToRiemannSphere (D.dev y)
    rw [realMobiusAction_realMobiusProjection]
    exact realMobiusRepresentative_projective_action A (D.dev y)

end HyperbolicDevelopingMap

namespace LiftedHyperbolicDevelopingMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- The projective developing map attached to a lifted hyperbolic developing map. -/
def projectiveDev (D : LiftedHyperbolicDevelopingMap X x₀ g) :
    D.cover.total → RiemannSphere :=
  fun y ↦ upperHalfPlaneToRiemannSphere (D.dev y)

@[simp]
theorem projectiveDev_apply (D : LiftedHyperbolicDevelopingMap X x₀ g)
    (y : D.cover.total) :
    D.projectiveDev y = upperHalfPlaneToRiemannSphere (D.dev y) :=
  rfl

/--
The projective equivariance obligation follows from lifted real equivariance:
use the complexified lifted holonomy representative for each loop.
-/
theorem projectiveEquivariant
    (D : LiftedHyperbolicDevelopingMap X x₀ g) :
    D.toHyperbolicDevelopingMap.ProjectiveEquivariant
      D.toHyperbolicDevelopingMap.projectiveHolonomy := by
  exact D.toHyperbolicDevelopingMap.projectiveEquivariant

end LiftedHyperbolicDevelopingMap

/--
Regularity of the projectivized developing map, inherited from the
upper-half-plane developing map through the finite inclusion `ℍ → ℂP¹`.
-/
structure ProjectivizedDevelopingMapRegularity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}
    (D : HyperbolicDevelopingMap X x₀ g) : Prop where
  /-- The finite affine coordinate expression is holomorphic in source charts. -/
  finite_chartwise_holomorphic : HyperbolicDevelopingMapHolomorphic D.cover D.dev
  /-- The finite affine coordinate expression has nonzero derivative. -/
  finite_local_biholomorphic : HyperbolicDevelopingMapLocallyBiholomorphic D.cover D.dev
  /-- The finite affine coordinate expression has local homeomorphism branch data. -/
  finite_local_biholomorphism_data :
    HyperbolicDevelopingMapLocalBiholomorphismData D.cover D.dev
  /-- In the finite chart of `ℂP¹`, projectivization is the usual inclusion. -/
  finite_coordinate_eq :
    ∀ y, D.projectiveDev y = (((D.dev y : ℍ) : ℂ) : RiemannSphere)

namespace HyperbolicDevelopingMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- Projectivization preserves the strengthened finite-coordinate regularity. -/
theorem projectivizedDevelopingMapRegularity
    (D : HyperbolicDevelopingMap X x₀ g) :
    ProjectivizedDevelopingMapRegularity D where
  finite_chartwise_holomorphic := D.dev_holomorphic
  finite_local_biholomorphic := D.dev_locally_biholomorphic
  finite_local_biholomorphism_data := D.dev_local_biholomorphism_data
  finite_coordinate_eq := by
    intro y
    rfl

end HyperbolicDevelopingMap

/--
%%handwave
name:
  Projectivized hyperbolic developing map
statement:
  A projectivized hyperbolic developing map packages a hyperbolic developing
  map $\operatorname{dev} : \widetilde X \to \mathbb H$ after composing it
  with the inclusion $\mathbb H \hookrightarrow \mathbb{CP}^1$. It carries the
  complexified projective holonomy, the inherited finite-coordinate regularity,
  and the projective equivariance data.
-/
structure ProjectivizedHyperbolicDevelopingMap (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] (x₀ : X)
    (g : HyperbolicMetric X) where
  /-- The original hyperbolic developing map. -/
  hyperbolicDevelopingMap : HyperbolicDevelopingMap X x₀ g
  /-- The complex projective holonomy. -/
  projectiveHolonomy : HolonomyRepresentation X x₀
  /-- The projective holonomy is induced from the real holonomy by complexification. -/
  projectiveHolonomy_complexifies_real :
    hyperbolicDevelopingMap.ProjectiveHolonomyComplexifiesReal projectiveHolonomy
  /-- The projectivized map has holomorphic finite-coordinate local-biholomorphic regularity. -/
  projective_regular :
    ProjectivizedDevelopingMapRegularity hyperbolicDevelopingMap
  /-- The composed developing map is equivariant for the complex projective holonomy. -/
  projective_equivariant :
    hyperbolicDevelopingMap.ProjectiveEquivariant projectiveHolonomy

namespace ProjectivizedHyperbolicDevelopingMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- The Riemann-sphere-valued developing map underlying a projectivized package. -/
def projectiveDev (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) :
    D.hyperbolicDevelopingMap.cover.total → RiemannSphere :=
  D.hyperbolicDevelopingMap.projectiveDev

@[simp]
theorem projectiveDev_apply (D : ProjectivizedHyperbolicDevelopingMap X x₀ g)
    (y : D.hyperbolicDevelopingMap.cover.total) :
    D.projectiveDev y =
      upperHalfPlaneToRiemannSphere (D.hyperbolicDevelopingMap.dev y) :=
  rfl

/-- The projective holonomy of a projectivized developing map is the complexified real holonomy. -/
theorem projectiveHolonomy_eq_complexified_real
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) :
    D.projectiveHolonomy.toMonoidHom =
      realMobiusToMobiusGroup.comp D.hyperbolicDevelopingMap.holonomy.toMonoidHom :=
  D.projectiveHolonomy_complexifies_real

/--
The projectivized holonomy of an upper-half-plane developing map is already
real, hence it admits the Mobius-postcomposition normalization with the
identity postcomposition.
-/
def projectiveHolonomyMobiusNormalization
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) :
    ProjectiveHolonomyMobiusNormalization x₀ D.projectiveHolonomy :=
  ProjectiveHolonomyMobiusNormalization.of_complexified_real
    D.hyperbolicDevelopingMap.holonomy D.projectiveHolonomy
    D.projectiveHolonomy_eq_complexified_real

@[simp]
theorem projectiveHolonomyMobiusNormalization_postcomposition
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) :
    D.projectiveHolonomyMobiusNormalization.postcomposition = 1 :=
  rfl

@[simp]
theorem projectiveHolonomyMobiusNormalization_realHolonomy
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) :
    D.projectiveHolonomyMobiusNormalization.realHolonomy =
      D.hyperbolicDevelopingMap.holonomy :=
  rfl

/--
For a hyperbolic developing map viewed projectively, the normalized holonomy
representation is just the original complexified holonomy: the required Mobius
postcomposition is the identity.
-/
theorem projectiveHolonomyMobiusNormalization_normalizedHolonomyRepresentation_eq
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) :
    D.projectiveHolonomyMobiusNormalization.normalizedHolonomyRepresentation.toMonoidHom =
      D.projectiveHolonomy.toMonoidHom := by
  ext γ
  simp [ProjectiveHolonomyMobiusNormalization.normalizedHolonomy,
    ProjectiveHolonomyMobiusNormalization.postcompositionClass]

/--
The normalized holonomy representation attached to the projectivization is a
literal complexification of the hyperbolic real holonomy.
-/
theorem projectiveHolonomyMobiusNormalization_normalizedHolonomyRepresentation_complexifies_real
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) :
    D.projectiveHolonomyMobiusNormalization.normalizedHolonomyRepresentation.IsComplexificationOfReal :=
  D.projectiveHolonomyMobiusNormalization.normalizedHolonomyRepresentation_isComplexificationOfReal

end ProjectivizedHyperbolicDevelopingMap

namespace HyperbolicDevelopingMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/--
Projectivize a hyperbolic developing map by composing `dev` with
`ℍ ⊂ ℂP¹` and complexifying its real holonomy.
-/
def toProjectivized (D : HyperbolicDevelopingMap X x₀ g)
    (h_equivariant : D.ProjectiveEquivariant D.projectiveHolonomy) :
    ProjectivizedHyperbolicDevelopingMap X x₀ g where
  hyperbolicDevelopingMap := D
  projectiveHolonomy := D.projectiveHolonomy
  projectiveHolonomy_complexifies_real := D.projectiveHolonomy_complexifies_real
  projective_regular := D.projectivizedDevelopingMapRegularity
  projective_equivariant := h_equivariant

@[simp]
theorem toProjectivized_hyperbolicDevelopingMap
    (D : HyperbolicDevelopingMap X x₀ g)
    (h_equivariant : D.ProjectiveEquivariant D.projectiveHolonomy) :
    (D.toProjectivized h_equivariant).hyperbolicDevelopingMap = D :=
  rfl

@[simp]
theorem toProjectivized_projectiveHolonomy
    (D : HyperbolicDevelopingMap X x₀ g)
    (h_equivariant : D.ProjectiveEquivariant D.projectiveHolonomy) :
    (D.toProjectivized h_equivariant).projectiveHolonomy = D.projectiveHolonomy :=
  rfl

end HyperbolicDevelopingMap

namespace LiftedHyperbolicDevelopingMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- Projectivize a lifted hyperbolic developing map. -/
def toProjectivized (D : LiftedHyperbolicDevelopingMap X x₀ g) :
    ProjectivizedHyperbolicDevelopingMap X x₀ g :=
  D.toHyperbolicDevelopingMap.toProjectivized D.projectiveEquivariant

@[simp]
theorem toProjectivized_hyperbolicDevelopingMap
    (D : LiftedHyperbolicDevelopingMap X x₀ g) :
    D.toProjectivized.hyperbolicDevelopingMap = D.toHyperbolicDevelopingMap :=
  rfl

end LiftedHyperbolicDevelopingMap

namespace HyperbolicDevelopingPipeline

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- The projectivized developing map produced by the full hyperbolic pipeline. -/
def toProjectivizedDevelopingMap
    (P : HyperbolicDevelopingPipeline X x₀ g) :
    ProjectivizedHyperbolicDevelopingMap X x₀ g :=
  P.toLiftedHyperbolicDevelopingMap.toProjectivized

@[simp]
theorem toProjectivizedDevelopingMap_hyperbolicDevelopingMap
    (P : HyperbolicDevelopingPipeline X x₀ g) :
    P.toProjectivizedDevelopingMap.hyperbolicDevelopingMap =
      P.toHyperbolicDevelopingMap :=
  rfl

end HyperbolicDevelopingPipeline

namespace HyperbolicDevelopingConstructionPipeline

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- The projectivized developing map produced by the refined construction pipeline. -/
def toProjectivizedDevelopingMap
    (P : HyperbolicDevelopingConstructionPipeline X x₀ g) :
    ProjectivizedHyperbolicDevelopingMap X x₀ g :=
  P.toHyperbolicDevelopingPipeline.toProjectivizedDevelopingMap

@[simp]
theorem toProjectivizedDevelopingMap_hyperbolicDevelopingMap
    (P : HyperbolicDevelopingConstructionPipeline X x₀ g) :
    P.toProjectivizedDevelopingMap.hyperbolicDevelopingMap =
      P.toHyperbolicDevelopingMap :=
  rfl

end HyperbolicDevelopingConstructionPipeline

namespace HyperbolicDevelopingCurvaturePipeline

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- The projectivized developing map produced by the curvature-aware pipeline. -/
def toProjectivizedDevelopingMap
    (P : HyperbolicDevelopingCurvaturePipeline X x₀ g) :
    ProjectivizedHyperbolicDevelopingMap X x₀ g :=
  P.toHyperbolicDevelopingPipeline.toProjectivizedDevelopingMap

@[simp]
theorem toProjectivizedDevelopingMap_hyperbolicDevelopingMap
    (P : HyperbolicDevelopingCurvaturePipeline X x₀ g) :
    P.toProjectivizedDevelopingMap.hyperbolicDevelopingMap =
      P.toHyperbolicDevelopingMap :=
  rfl

end HyperbolicDevelopingCurvaturePipeline

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/-- Target package: a hyperbolic metric has a projectivized developing map. -/
def AdmitsProjectivizedDevelopingMap (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (ProjectivizedHyperbolicDevelopingMap X x₀ g)

theorem admitsProjectivizedDevelopingMap_of_admitsLiftedDevelopingMap
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsLiftedDevelopingMap x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  h.elim fun D ↦ ⟨D.toProjectivized⟩

/-- A PSL-valued hyperbolic developing map projectivizes without choosing an `SL(2, ℝ)` lift. -/
theorem admitsProjectivizedDevelopingMap_of_admitsDevelopingMap
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsDevelopingMap x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  h.elim fun D ↦ ⟨D.toProjectivized D.projectiveEquivariant⟩

theorem admitsProjectivizedDevelopingMap_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingPipeline x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  h.elim fun P ↦ ⟨P.toProjectivizedDevelopingMap⟩

theorem admitsProjectivizedDevelopingMap_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  h.elim fun P ↦ ⟨P.toProjectivizedDevelopingMap⟩

theorem admitsProjectivizedDevelopingMap_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  h.elim fun P ↦ ⟨P.toProjectivizedDevelopingMap⟩

end HyperbolicMetric

structure ProjectiveDevelopingBranchLocalHomeomorphismData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {g : HyperbolicMetric X}
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g)
    (chart : ProjectiveChart X)
    (lift : chart.source → D.hyperbolicDevelopingMap.cover.total) where
  /-- The descended developing branch is exactly the stored projective chart. -/
  chart_eq_projective_branch :
    ∀ x : chart.source, chart (x : X) = D.projectiveDev (lift x)
  /-- The descended projective developing branch is continuous. -/
  projective_branch_continuous :
    Continuous (fun x : chart.source ↦ D.projectiveDev (lift x))
  /-- A finite complex coordinate expression for the descended projective branch. -/
  branchFiniteCoordinate : ℂ → ℂ
  /-- The single ambient complex chart used to express this branch. -/
  sourceComplexChart : OpenPartialHomeomorph X ℂ
  /-- The fixed complex chart belongs to the Riemann-surface atlas. -/
  sourceComplexChart_mem_atlas : sourceComplexChart ∈ atlas ℂ X
  /-- The complex-coordinate neighborhood on which the finite expression is used. -/
  fixedCoordinateSource : Set ℂ
  /-- The fixed coordinate source is open. -/
  fixedCoordinateSource_open : IsOpen fixedCoordinateSource
  /-- The fixed coordinate source lies in the target of the chosen complex chart. -/
  fixedCoordinateSource_subset_chart_target :
    fixedCoordinateSource ⊆ sourceComplexChart.target
  /-- The projective branch source is covered by the chosen complex chart. -/
  chart_source_subset_sourceComplexChart_source :
    chart.source ⊆ sourceComplexChart.source
  /-- Every point of the projective chart source is represented in the fixed coordinate source. -/
  chart_source_maps_to_fixedCoordinateSource :
    ∀ x : chart.source, sourceComplexChart (x : X) ∈ fixedCoordinateSource
  /--
  The finite coordinate expresses the projectivized developing branch in the
  chosen fixed complex chart.
  -/
  fixedCoordinate_eq_projective_branch :
    ∀ x : chart.source,
      D.projectiveDev (lift x) =
        (branchFiniteCoordinate (sourceComplexChart (x : X)) : RiemannSphere)
  /--
  The same equality holds on the fixed coordinate neighborhood wherever the
  inverse complex chart lands in the branch source.
  -/
  fixedCoordinate_eq_on_source :
    ∀ z ∈ fixedCoordinateSource,
      ∀ hz : sourceComplexChart.symm z ∈ chart.source,
        D.projectiveDev (lift ⟨sourceComplexChart.symm z, hz⟩) =
          (branchFiniteCoordinate z : RiemannSphere)
  /-- The finite branch coordinate is holomorphic on the fixed coordinate source. -/
  branchFiniteCoordinate_holomorphic :
    ∀ z ∈ fixedCoordinateSource, DifferentiableAt ℂ branchFiniteCoordinate z
  /-- The finite branch coordinate has nonzero derivative on the fixed coordinate source. -/
  branchFiniteCoordinate_deriv_ne_zero :
    ∀ z ∈ fixedCoordinateSource, deriv branchFiniteCoordinate z ≠ 0
  /-- The projective chart source is open in the surface. -/
  source_open : IsOpen chart.source
  /-- The projective chart target is open in the Riemann sphere. -/
  target_open : IsOpen chart.target
  /-- The stored chart maps its source into its target. -/
  chart_maps_source :
    ∀ x : chart.source, chart (x : X) ∈ chart.target
  /-- The stored inverse chart maps its target back to its source. -/
  chart_symm_maps_target :
    ∀ z : chart.target, chart.symm (z : RiemannSphere) ∈ chart.source
  /-- The stored inverse chart is a left inverse on the source. -/
  chart_left_inv :
    ∀ x : chart.source, chart.symm (chart (x : X)) = (x : X)
  /-- The stored chart is a left inverse to its inverse on the target. -/
  chart_right_inv :
    ∀ z : chart.target, chart (chart.symm (z : RiemannSphere)) = (z : RiemannSphere)

namespace ProjectiveDevelopingBranchLocalHomeomorphismData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {g : HyperbolicMetric X}
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}
    {chart : ProjectiveChart X}
    {lift : chart.source → D.hyperbolicDevelopingMap.cover.total}

/--
Construct the branch-local-homeomorphism certificate from the actual descended
branch identity and continuity.  The local homeomorphism part is supplied by
the stored `OpenPartialHomeomorph` chart itself.
-/
def of_chart_eq_projective_branch
    (hbranch : ∀ x : chart.source, chart (x : X) = D.projectiveDev (lift x))
    (hcontinuous : Continuous (fun x : chart.source ↦ D.projectiveDev (lift x)))
    (branchFiniteCoordinate : ℂ → ℂ)
    (sourceComplexChart : OpenPartialHomeomorph X ℂ)
    (sourceComplexChart_mem_atlas : sourceComplexChart ∈ atlas ℂ X)
    (fixedCoordinateSource : Set ℂ)
    (fixedCoordinateSource_open : IsOpen fixedCoordinateSource)
    (fixedCoordinateSource_subset_chart_target :
      fixedCoordinateSource ⊆ sourceComplexChart.target)
    (chart_source_subset_sourceComplexChart_source :
      chart.source ⊆ sourceComplexChart.source)
    (chart_source_maps_to_fixedCoordinateSource :
      ∀ x : chart.source, sourceComplexChart (x : X) ∈ fixedCoordinateSource)
    (hfinite_eq :
      ∀ x : chart.source,
        D.projectiveDev (lift x) =
          (branchFiniteCoordinate (sourceComplexChart (x : X)) : RiemannSphere))
    (hfinite_eq_on_source :
      ∀ z ∈ fixedCoordinateSource,
        ∀ hz : sourceComplexChart.symm z ∈ chart.source,
          D.projectiveDev (lift ⟨sourceComplexChart.symm z, hz⟩) =
            (branchFiniteCoordinate z : RiemannSphere))
    (hfinite_holomorphic :
      ∀ z ∈ fixedCoordinateSource, DifferentiableAt ℂ branchFiniteCoordinate z)
    (hfinite_deriv_ne_zero :
      ∀ z ∈ fixedCoordinateSource, deriv branchFiniteCoordinate z ≠ 0) :
    ProjectiveDevelopingBranchLocalHomeomorphismData X D chart lift where
  chart_eq_projective_branch := hbranch
  projective_branch_continuous := hcontinuous
  branchFiniteCoordinate := branchFiniteCoordinate
  sourceComplexChart := sourceComplexChart
  sourceComplexChart_mem_atlas := sourceComplexChart_mem_atlas
  fixedCoordinateSource := fixedCoordinateSource
  fixedCoordinateSource_open := fixedCoordinateSource_open
  fixedCoordinateSource_subset_chart_target := fixedCoordinateSource_subset_chart_target
  chart_source_subset_sourceComplexChart_source :=
    chart_source_subset_sourceComplexChart_source
  chart_source_maps_to_fixedCoordinateSource := chart_source_maps_to_fixedCoordinateSource
  fixedCoordinate_eq_projective_branch := hfinite_eq
  fixedCoordinate_eq_on_source := hfinite_eq_on_source
  branchFiniteCoordinate_holomorphic := hfinite_holomorphic
  branchFiniteCoordinate_deriv_ne_zero := hfinite_deriv_ne_zero
  source_open := chart.open_source
  target_open := chart.open_target
  chart_maps_source := by
    intro x
    exact chart.map_source x.2
  chart_symm_maps_target := by
    intro z
    exact chart.symm.map_source z.2
  chart_left_inv := by
    intro x
    exact chart.left_inv x.2
  chart_right_inv := by
    intro z
    exact chart.right_inv z.2

/--
The selected finite coordinate for a developing branch gives concrete
projective/complex chart compatibility with the complex chart used to define
that branch.
-/
def toProjectiveComplexChartCompatibilityData
    (B : ProjectiveDevelopingBranchLocalHomeomorphismData X D chart lift) :
    ProjectiveComplexChartCompatibilityData chart B.sourceComplexChart where
  representative := 1
  finiteCoordinate := B.branchFiniteCoordinate
  finiteCoordinate_eq := by
    intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    have hzTarget : z ∈ B.sourceComplexChart.target := by
      simpa [OpenPartialHomeomorph.symm_source] using hz.1
    have hzChart : B.sourceComplexChart.symm z ∈ chart.source := hz.2
    have hzFixed : z ∈ B.fixedCoordinateSource := by
      have h :=
        B.chart_source_maps_to_fixedCoordinateSource
          ⟨B.sourceComplexChart.symm z, hzChart⟩
      simpa [B.sourceComplexChart.right_inv hzTarget] using h
    have hfinite := B.fixedCoordinate_eq_on_source z hzFixed hzChart
    have hbranch :=
      B.chart_eq_projective_branch ⟨B.sourceComplexChart.symm z, hzChart⟩
    calc
      (1 : MobiusRepresentative) •
          ((B.sourceComplexChart.symm.trans chart) z) =
          (B.sourceComplexChart.symm.trans chart) z := by
        simp
      _ = chart (B.sourceComplexChart.symm z) := by
        simp [OpenPartialHomeomorph.trans_apply]
      _ = D.projectiveDev
          (lift ⟨B.sourceComplexChart.symm z, hzChart⟩) := hbranch
      _ = (B.branchFiniteCoordinate z : RiemannSphere) := hfinite
  finiteCoordinate_holomorphic := by
    intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    have hzTarget : z ∈ B.sourceComplexChart.target := by
      simpa [OpenPartialHomeomorph.symm_source] using hz.1
    have hzChart : B.sourceComplexChart.symm z ∈ chart.source := hz.2
    have hzFixed : z ∈ B.fixedCoordinateSource := by
      have h :=
        B.chart_source_maps_to_fixedCoordinateSource
          ⟨B.sourceComplexChart.symm z, hzChart⟩
      simpa [B.sourceComplexChart.right_inv hzTarget] using h
    exact B.branchFiniteCoordinate_holomorphic z hzFixed
  finiteCoordinate_deriv_ne_zero := by
    intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    have hzTarget : z ∈ B.sourceComplexChart.target := by
      simpa [OpenPartialHomeomorph.symm_source] using hz.1
    have hzChart : B.sourceComplexChart.symm z ∈ chart.source := hz.2
    have hzFixed : z ∈ B.fixedCoordinateSource := by
      have h :=
        B.chart_source_maps_to_fixedCoordinateSource
          ⟨B.sourceComplexChart.symm z, hzChart⟩
      simpa [B.sourceComplexChart.right_inv hzTarget] using h
    exact B.branchFiniteCoordinate_deriv_ne_zero z hzFixed
  finiteCoordinate_local := by
    intro z hz
    refine ⟨(B.sourceComplexChart.symm.trans chart).source,
      (B.sourceComplexChart.symm.trans chart).open_source, hz, subset_rfl, ?_⟩
    intro w hw
    constructor
    · rw [OpenPartialHomeomorph.trans_source] at hw
      have hwTarget : w ∈ B.sourceComplexChart.target := by
        simpa [OpenPartialHomeomorph.symm_source] using hw.1
      have hwChart : B.sourceComplexChart.symm w ∈ chart.source := hw.2
      have hwFixed : w ∈ B.fixedCoordinateSource := by
        have h :=
          B.chart_source_maps_to_fixedCoordinateSource
            ⟨B.sourceComplexChart.symm w, hwChart⟩
        simpa [B.sourceComplexChart.right_inv hwTarget] using h
      exact B.branchFiniteCoordinate_holomorphic w hwFixed
    · rw [OpenPartialHomeomorph.trans_source] at hw
      have hwTarget : w ∈ B.sourceComplexChart.target := by
        simpa [OpenPartialHomeomorph.symm_source] using hw.1
      have hwChart : B.sourceComplexChart.symm w ∈ chart.source := hw.2
      have hwFixed : w ∈ B.fixedCoordinateSource := by
        have h :=
          B.chart_source_maps_to_fixedCoordinateSource
            ⟨B.sourceComplexChart.symm w, hwChart⟩
        simpa [B.sourceComplexChart.right_inv hwTarget] using h
      exact B.branchFiniteCoordinate_deriv_ne_zero w hwFixed

end ProjectiveDevelopingBranchLocalHomeomorphismData

/--
A local projective chart obtained from a projectivized developing map.

The field `lift` is the local inverse branch of the covering projection used to
pull the single-valued developing map on the cover down to a projective chart
on `X`.
-/
structure ProjectiveLocalChartFromDevelopingMap (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] {x₀ : X}
    {g : HyperbolicMetric X} (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) where
  /-- The descended projective chart on `X`. -/
  chart : ProjectiveChart X
  /-- A local lift of points in the chart source to the simply connected cover. -/
  lift : chart.source → D.hyperbolicDevelopingMap.cover.total
  /-- The local lift projects back to the original point. -/
  lift_projects :
    ∀ x : chart.source, D.hyperbolicDevelopingMap.cover.projection (lift x) = (x : X)
  /-- The chart is the projective developing map evaluated on the local lift. -/
  chart_eq_projectiveDev : ∀ x : chart.source,
    chart (x : X) = D.projectiveDev (lift x)
  /-- The local lift is continuous on the chart source. -/
  lift_continuous : Continuous lift
  /-- The descended developing branch has the concrete regularity needed of a local chart. -/
  branch_local_homeomorphism :
    ProjectiveDevelopingBranchLocalHomeomorphismData X D chart lift

namespace ProjectiveLocalChartFromDevelopingMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}

/-- Points in the local chart source are represented by their chosen lift. -/
theorem projection_lift
    (C : ProjectiveLocalChartFromDevelopingMap X D) (x : C.chart.source) :
    D.hyperbolicDevelopingMap.cover.projection (C.lift x) = (x : X) :=
  C.lift_projects x

/-- On a local branch, the projective chart agrees with the developing map. -/
theorem chart_apply_eq_projectiveDev
    (C : ProjectiveLocalChartFromDevelopingMap X D) (x : C.chart.source) :
    C.chart (x : X) = D.projectiveDev (C.lift x) :=
  C.chart_eq_projectiveDev x

theorem lift_continuous'
    (C : ProjectiveLocalChartFromDevelopingMap X D) :
    Continuous C.lift :=
  C.lift_continuous

def branch_local_homeomorphism'
    (C : ProjectiveLocalChartFromDevelopingMap X D) :
    ProjectiveDevelopingBranchLocalHomeomorphismData X D C.chart C.lift :=
  C.branch_local_homeomorphism

/-- The branch-local-homeomorphism certificate also identifies the branch with the chart. -/
theorem branch_chart_eq_projectiveDev
    (C : ProjectiveLocalChartFromDevelopingMap X D) (x : C.chart.source) :
    C.chart (x : X) = D.projectiveDev (C.lift x) :=
  C.branch_local_homeomorphism.chart_eq_projective_branch x

/-- The descended projective developing branch is continuous. -/
theorem projective_branch_continuous
    (C : ProjectiveLocalChartFromDevelopingMap X D) :
    Continuous (fun x : C.chart.source ↦ D.projectiveDev (C.lift x)) :=
  C.branch_local_homeomorphism.projective_branch_continuous

/-- The source of a branch chart is open. -/
theorem source_open
    (C : ProjectiveLocalChartFromDevelopingMap X D) :
    IsOpen C.chart.source :=
  C.branch_local_homeomorphism.source_open

/-- The target of a branch chart is open. -/
theorem target_open
    (C : ProjectiveLocalChartFromDevelopingMap X D) :
    IsOpen C.chart.target :=
  C.branch_local_homeomorphism.target_open

/-- The source of a developing branch is covered by its selected complex chart. -/
theorem source_subset_sourceComplexChart_source
    (C : ProjectiveLocalChartFromDevelopingMap X D) :
    C.chart.source ⊆ C.branch_local_homeomorphism.sourceComplexChart.source :=
  C.branch_local_homeomorphism.chart_source_subset_sourceComplexChart_source

/-- A developing branch is compatible with its selected source complex chart. -/
def sourceComplexChartCompatibility
    (C : ProjectiveLocalChartFromDevelopingMap X D) :
    ProjectiveComplexChartCompatibilityData C.chart
      C.branch_local_homeomorphism.sourceComplexChart :=
  C.branch_local_homeomorphism.toProjectiveComplexChartCompatibilityData

end ProjectiveLocalChartFromDevelopingMap

structure ProjectiveDevelopingAtlasRiemannSurfaceCompatibilityData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {g : HyperbolicMetric X}
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}
    (chartAt : X → ProjectiveLocalChartFromDevelopingMap X D) where
  /-- Each selected projective developing chart has open source. -/
  projective_source_open : ∀ x, IsOpen (chartAt x).chart.source
  /-- Ambient complex chart sources are open in the same surface topology. -/
  complex_source_open : ∀ e ∈ atlas ℂ X, IsOpen e.source
  /--
  Developing charts are holomorphically compatible with the selected ambient
  complex charts used to construct them.
  -/
  projective_complex_compatible :
    ∀ x, ProjectiveComplexChartCompatibilityData (chartAt x).chart
      (chartAt x).branch_local_homeomorphism.sourceComplexChart

/--
Selected Riemann-surface compatibility for a developing atlas.

This is the compatibility supplied directly by the constructed local branches:
each projective branch is holomorphic and locally biholomorphic in the ambient
complex chart chosen with its cover-local section.
-/
structure ProjectiveDevelopingAtlasSelectedRiemannSurfaceCompatibilityData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {g : HyperbolicMetric X}
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}
    (chartAt : X → ProjectiveLocalChartFromDevelopingMap X D) where
  /-- Each selected projective developing chart has open source. -/
  projective_source_open : ∀ x, IsOpen (chartAt x).chart.source
  /-- Ambient complex chart sources are open in the same surface topology. -/
  complex_source_open : ∀ e ∈ atlas ℂ X, IsOpen e.source
  /--
  Each selected developing chart is holomorphically compatible with the
  selected ambient complex chart used to construct it.
  -/
  selected_projective_complex_compatible :
    ∀ x, ProjectiveComplexChartCompatibilityData (chartAt x).chart
      (chartAt x).branch_local_homeomorphism.sourceComplexChart

namespace ProjectiveDevelopingAtlasSelectedRiemannSurfaceCompatibilityData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}

/--
Any atlas of developing branch charts has selected Riemann-surface
compatibility, because that compatibility is stored on each local branch.
-/
def ofChartAt
    (chartAt : X → ProjectiveLocalChartFromDevelopingMap X D) :
    ProjectiveDevelopingAtlasSelectedRiemannSurfaceCompatibilityData X chartAt where
  projective_source_open := fun x ↦ (chartAt x).source_open
  complex_source_open := fun e _he ↦ e.open_source
  selected_projective_complex_compatible := fun x ↦
    (chartAt x).sourceComplexChartCompatibility

end ProjectiveDevelopingAtlasSelectedRiemannSurfaceCompatibilityData

namespace ProjectiveDevelopingAtlasRiemannSurfaceCompatibilityData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}

/--
Any atlas of constructed developing branch charts has Riemann-surface
compatibility in the selected source complex charts.
-/
def ofChartAt
    (chartAt : X → ProjectiveLocalChartFromDevelopingMap X D) :
    ProjectiveDevelopingAtlasRiemannSurfaceCompatibilityData X chartAt where
  projective_source_open := fun x ↦ (chartAt x).source_open
  complex_source_open := fun e _he ↦ e.open_source
  projective_complex_compatible := fun x ↦
    (chartAt x).sourceComplexChartCompatibility

end ProjectiveDevelopingAtlasRiemannSurfaceCompatibilityData

def ProjectiveDevelopingAtlasRiemannSurfaceCompatibilityBoundary
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {g : HyperbolicMetric X}
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}
    (chartAt : X → ProjectiveLocalChartFromDevelopingMap X D) : Prop :=
  Nonempty (ProjectiveDevelopingAtlasRiemannSurfaceCompatibilityData X chartAt)

/--
An atlas worth of projective charts obtained from a projectivized developing
map.
-/
structure ProjectiveDevelopingAtlasData (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] {x₀ : X}
    {g : HyperbolicMetric X} (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) where
  /-- A projective developing chart near each point of `X`. -/
  chartAt : X → ProjectiveLocalChartFromDevelopingMap X D
  /-- The chosen chart near `x` contains `x`. -/
  mem_chartAt_source : ∀ x, x ∈ (chartAt x).chart.source
  /-- Coordinate changes between these local charts are locally Mobius. -/
  transition_mobius : ∀ x y, HasLocalMobiusTransition (chartAt x).chart (chartAt y).chart
  /-- These charts are compatible with the original Riemann surface structure. -/
  compatible_with_riemann_surface :
    ProjectiveDevelopingAtlasRiemannSurfaceCompatibilityData X chartAt

namespace ProjectiveDevelopingAtlasData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}

/-- The local developing charts cover the whole surface. -/
theorem source_cover (A : ProjectiveDevelopingAtlasData X D) :
    (⋃ x : X, (A.chartAt x).chart.source) = Set.univ := by
  ext y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    exact Set.mem_iUnion.mpr ⟨y, A.mem_chartAt_source y⟩

/-- The preferred local developing chart at `x`. -/
def localChartAt (A : ProjectiveDevelopingAtlasData X D) (x : X) :
    ProjectiveChart X :=
  (A.chartAt x).chart

theorem localChartAt_transition_mobius
    (A : ProjectiveDevelopingAtlasData X D) (x y : X) :
    HasLocalMobiusTransition (A.localChartAt x) (A.localChartAt y) :=
  A.transition_mobius x y

/-- The selected projective chart at `x` has open source. -/
theorem localChartAt_source_open
    (A : ProjectiveDevelopingAtlasData X D) (x : X) :
    IsOpen (A.localChartAt x).source :=
  A.compatible_with_riemann_surface.projective_source_open x

/-- The selected developing chart is compatible with its selected complex chart. -/
def localChartAt_complex_compatible
    (A : ProjectiveDevelopingAtlasData X D) (x : X) :
    ProjectiveComplexChartCompatibilityData (A.localChartAt x)
      (A.chartAt x).branch_local_homeomorphism.sourceComplexChart :=
  A.compatible_with_riemann_surface.projective_complex_compatible x

end ProjectiveDevelopingAtlasData

/--
%%handwave
name:
  Projective atlas from a developing map
statement:
  This package says that the local inverse branches of a projectivized
  developing map descend from the cover to projective charts on $X$, and that
  these charts assemble into a complex projective structure with the expected
  holonomy.
-/
structure ProjectiveAtlasFromDevelopingMap (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] {x₀ : X}
    {g : HyperbolicMetric X} (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) where
  /-- The local branch atlas from which the projective structure is built. -/
  developingAtlas : ProjectiveDevelopingAtlasData X D
  /-- The complex projective structure obtained from local inverse branches of `D`. -/
  projectiveStructure : ComplexProjectiveStructure X
  /-- The holonomy representation attached to the constructed atlas. -/
  projectiveHolonomy : HolonomyRepresentation X x₀
  /-- The atlas holonomy agrees with the holonomy of the projectivized developing map. -/
  projectiveHolonomy_eq : projectiveHolonomy = D.projectiveHolonomy
  /-- Projective charts are locally obtained from branches of the developing map. -/
  charts_are_local_inverse_branches : ∀ x,
    (developingAtlas.chartAt x).chart ∈ projectiveStructure.atlasSet
  /-- Local Mobius transition maps come from projective equivariance. -/
  transition_mobius_from_equivariance :
    ∀ x y, HasLocalMobiusTransition (developingAtlas.chartAt x).chart
      (developingAtlas.chartAt y).chart
  /--
  Every chart of the stored projective structure is locally Mobius-equivalent
  to one of the selected developing branches.
  -/
  atlas_charts_locally_mobius_equiv_to_developing_branches :
    ∀ e ∈ projectiveStructure.atlasSet, ∀ x ∈ e.source,
      ∃ y, x ∈ (developingAtlas.chartAt y).chart.source ∧
        HasLocalMobiusTransition e (developingAtlas.chartAt y).chart
  /-- The constructed projective atlas induces the original Riemann surface structure. -/
  compatible_with_riemann_surface_from_developing_map :
    ProjectiveDevelopingAtlasRiemannSurfaceCompatibilityData X
      developingAtlas.chartAt

namespace ProjectiveAtlasFromDevelopingMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}

/-- The local projective chart from the developing map near `x`. -/
def localChartAt (A : ProjectiveAtlasFromDevelopingMap X D) (x : X) :
    ProjectiveChart X :=
  (A.developingAtlas.chartAt x).chart

theorem localChartAt_mem_atlas
    (A : ProjectiveAtlasFromDevelopingMap X D) (x : X) :
    A.localChartAt x ∈ A.projectiveStructure.atlasSet :=
  A.charts_are_local_inverse_branches x

theorem localChartAt_transition_mobius
    (A : ProjectiveAtlasFromDevelopingMap X D) (x y : X) :
    HasLocalMobiusTransition (A.localChartAt x) (A.localChartAt y) :=
  A.transition_mobius_from_equivariance x y

theorem atlas_chart_locally_mobius_equiv_to_developing_branch
    (A : ProjectiveAtlasFromDevelopingMap X D)
    {e : ProjectiveChart X} (he : e ∈ A.projectiveStructure.atlasSet)
    {x : X} (hx : x ∈ e.source) :
    ∃ y, x ∈ (A.developingAtlas.chartAt y).chart.source ∧
      HasLocalMobiusTransition e (A.developingAtlas.chartAt y).chart :=
  A.atlas_charts_locally_mobius_equiv_to_developing_branches e he x hx

theorem localChartAt_source_cover
    (A : ProjectiveAtlasFromDevelopingMap X D) :
    (⋃ x : X, (A.localChartAt x).source) = Set.univ :=
  A.developingAtlas.source_cover

/-- The developing atlas is compatible with the original Riemann surface structure. -/
def compatible_with_riemann_surface
    (A : ProjectiveAtlasFromDevelopingMap X D) :
    ProjectiveDevelopingAtlasRiemannSurfaceCompatibilityData X
      A.developingAtlas.chartAt :=
  A.compatible_with_riemann_surface_from_developing_map

/--
The holonomy attached to the constructed projective atlas is the complexified
real holonomy of the original hyperbolic developing map.
-/
theorem projectiveHolonomy_eq_complexified_real
    (A : ProjectiveAtlasFromDevelopingMap X D) :
    A.projectiveHolonomy.toMonoidHom =
      realMobiusToMobiusGroup.comp D.hyperbolicDevelopingMap.holonomy.toMonoidHom := by
  rw [A.projectiveHolonomy_eq]
  exact D.projectiveHolonomy_eq_complexified_real

/--
%%handwave
name:
  Holonomy of the developing atlas is real
statement:
  Let $\operatorname{dev}:\widetilde X_{x_0}\to\mathbb H$ have holonomy
  $\rho:\pi_1(X,x_0)\to\mathrm{PSL}_2(\mathbb R)$, and let $P$ be the complex
  projective structure assembled from local branches of
  $\iota\circ\operatorname{dev}$. Then the projective holonomy of $P$ is the
  complexification $\iota_*\rho$; in particular, $P$ has
  $\mathrm{PSL}_2(\mathbb R)$ holonomy.
proof:
  Use the chosen branch at $x_0$ as base chart. For a lifted point, deck
  transitivity moves the selected local lift to that point, and projective
  equivariance identifies the corresponding chart with a Möbius translate of
  the selected branch. Thus the atlas holonomy is precisely $\iota_*\rho$.
-/
theorem hasPSL2RHolonomy (A : ProjectiveAtlasFromDevelopingMap X D) :
    HasPSL2RHolonomy x₀ A.projectiveStructure :=
  ⟨{
    projectiveHolonomy := A.projectiveHolonomy
    holonomy_constructed_from_projective_charts :=
      { developingData := {
          cover := D.hyperbolicDevelopingMap.cover
          developingMap := D.projectiveDev
          equivariant_representatives := by
            intro γ
            rcases D.projective_equivariant γ with ⟨M, hM, hdev⟩
            refine ⟨M, ?_, hdev⟩
            simpa [A.projectiveHolonomy_eq] using hM }
        baseChart := A.localChartAt x₀
        baseChart_mem := A.localChartAt_mem_atlas x₀
        basepoint_mem_baseChart := A.developingAtlas.mem_chartAt_source x₀
        developingMap_locally_agrees_with_projective_charts := by
          intro y
          let x := D.hyperbolicDevelopingMap.cover.projection y
          let C := A.developingAtlas.chartAt x
          have hx : x ∈ C.chart.source := A.developingAtlas.mem_chartAt_source x
          let u : D.hyperbolicDevelopingMap.cover.total := C.lift ⟨x, hx⟩
          have hu_fiber :
              D.hyperbolicDevelopingMap.cover.projection u =
                D.hyperbolicDevelopingMap.cover.projection y := by
            simpa [u, x] using C.lift_projects ⟨x, hx⟩
          rcases D.hyperbolicDevelopingMap.cover.deckAction_same_fiber_transitive
              u y hu_fiber with
            ⟨γ, hγ⟩
          rcases D.projective_equivariant γ with ⟨M, _hM, hdev⟩
          exact ⟨{
            chart := C.chart
            chart_mem := by
              simpa [C] using A.localChartAt_mem_atlas x
            projected_mem := by
              simpa [x, C] using hx
            lift := fun z ↦
              D.hyperbolicDevelopingMap.cover.deckAction γ (C.lift z)
            lift_projects := by
              intro z
              calc
                D.hyperbolicDevelopingMap.cover.projection
                    (D.hyperbolicDevelopingMap.cover.deckAction γ (C.lift z)) =
                    D.hyperbolicDevelopingMap.cover.projection (C.lift z) := by
                  exact D.hyperbolicDevelopingMap.cover.projection_deckAction γ
                    (C.lift z)
                _ = (z : X) := C.lift_projects z
            lift_through_y := by
              simpa [u, x, C] using hγ
            lift_continuous :=
              (D.hyperbolicDevelopingMap.cover.deckTransformation γ).continuous.comp
                C.lift_continuous
            normalization := M
            developing_eq_normalized_chart := by
              intro z
              calc
                D.projectiveDev
                    (D.hyperbolicDevelopingMap.cover.deckAction γ (C.lift z)) =
                    M • D.projectiveDev (C.lift z) := hdev (C.lift z)
                _ = M • C.chart (z : X) := by
                  rw [C.chart_eq_projectiveDev z]
          }⟩
        transition_mobius := by
          intro e he e' he'
          exact A.projectiveStructure.transition_mobius_of_mem he he' }
    realHolonomy := D.hyperbolicDevelopingMap.holonomy
    projectiveHolonomy_eq_real := A.projectiveHolonomy_eq_complexified_real
  }⟩

/--
The holonomy attached to the projective atlas constructed from a hyperbolic
developing map has the identity Mobius normalization into `PSL(2, ℝ)`.
-/
def projectiveHolonomyMobiusNormalization
    (A : ProjectiveAtlasFromDevelopingMap X D) :
    ProjectiveHolonomyMobiusNormalization x₀ A.projectiveHolonomy :=
  ProjectiveHolonomyMobiusNormalization.of_complexified_real
    D.hyperbolicDevelopingMap.holonomy A.projectiveHolonomy
    A.projectiveHolonomy_eq_complexified_real

@[simp]
theorem projectiveHolonomyMobiusNormalization_postcomposition
    (A : ProjectiveAtlasFromDevelopingMap X D) :
    A.projectiveHolonomyMobiusNormalization.postcomposition = 1 :=
  rfl

/--
The normalized holonomy representation of the atlas is still the original
complexified real holonomy.
-/
theorem projectiveHolonomyMobiusNormalization_normalizedHolonomyRepresentation_complexifies_real
    (A : ProjectiveAtlasFromDevelopingMap X D) :
    A.projectiveHolonomyMobiusNormalization.normalizedHolonomyRepresentation.IsComplexificationOfReal :=
  A.projectiveHolonomyMobiusNormalization.normalizedHolonomyRepresentation_isComplexificationOfReal

/-- The atlas holonomy is conjugate into `PSL(2, ℝ)`. -/
theorem projectiveHolonomy_isConjugateIntoPSL2R
    (A : ProjectiveAtlasFromDevelopingMap X D) :
    A.projectiveHolonomy.IsConjugateIntoPSL2R :=
  ⟨A.projectiveHolonomyMobiusNormalization⟩

end ProjectiveAtlasFromDevelopingMap

/--
A projective structure has verified real holonomy from a hyperbolic developing
atlas when it is literally the projective structure generated from that atlas,
and the atlas holonomy is the complexification of the underlying real
hyperbolic holonomy.
-/
structure ComplexProjectiveStructure.VerifiedRealHolonomyFromHyperbolicDevelopingAtlas
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) (g : HyperbolicMetric X)
    (P : ComplexProjectiveStructure X) where
  /-- The projectivized hyperbolic developing map. -/
  projectivizedDevelopingMap : ProjectivizedHyperbolicDevelopingMap X x₀ g
  /-- The atlas constructed from local branches of the projectivized developing map. -/
  atlasFromDevelopingMap :
    ProjectiveAtlasFromDevelopingMap X projectivizedDevelopingMap
  /-- The stored projective structure is the one generated by the developing atlas. -/
  projectiveStructure_eq :
    atlasFromDevelopingMap.projectiveStructure = P
  /-- The atlas holonomy is the complexification of the hyperbolic real holonomy. -/
  projectiveHolonomy_eq_complexified_real :
    atlasFromDevelopingMap.projectiveHolonomy.toMonoidHom =
      realMobiusToMobiusGroup.comp
        projectivizedDevelopingMap.hyperbolicDevelopingMap.holonomy.toMonoidHom

/--
%%handwave
name:
  Hyperbolic induced projective structure
statement:
  A hyperbolic induced projective structure stores the hyperbolic developing
  map, its projectivization, and the projective atlas constructed from local
  branches. It is the concrete witness that a hyperbolic metric has produced a
  complex projective structure with $\mathrm{PSL}_2(\mathbb R)$ holonomy.
-/
structure HyperbolicInducedProjectiveStructure (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] (x₀ : X)
    (g : HyperbolicMetric X) where
  /-- The hyperbolic developing map producing the projective structure. -/
  developingMap : HyperbolicDevelopingMap X x₀ g
  /-- The developing map after composition with `ℍ ⊂ ℂP¹`, together with holonomy comparison. -/
  projectivizedDevelopingMap : ProjectivizedHyperbolicDevelopingMap X x₀ g
  /-- The projectivized package uses the same hyperbolic developing map. -/
  projectivized_developingMap_eq :
    projectivizedDevelopingMap.hyperbolicDevelopingMap = developingMap
  /-- The induced complex projective structure. -/
  projectiveStructure : ComplexProjectiveStructure X
  /-- The complex projective holonomy. -/
  projectiveHolonomy : HolonomyRepresentation X x₀
  /-- The projectivized package uses the same complex projective holonomy. -/
  projectivized_holonomy_eq :
    projectivizedDevelopingMap.projectiveHolonomy = projectiveHolonomy
  /-- The projective atlas obtained from local branches of the developing map. -/
  atlasFromDevelopingMap :
    ProjectiveAtlasFromDevelopingMap X projectivizedDevelopingMap
  /-- The stored projective structure is the one generated by the developing atlas. -/
  projectiveStructure_eq_atlas :
    projectiveStructure = atlasFromDevelopingMap.projectiveStructure
  /-- The stored projective holonomy is the holonomy of the developing atlas. -/
  projectiveHolonomy_eq_atlas :
    projectiveHolonomy = atlasFromDevelopingMap.projectiveHolonomy
  /-- The complex projective holonomy is the complexification of the real holonomy. -/
  holonomy_matches_real_holonomy :
    projectiveHolonomy.toMonoidHom =
      realMobiusToMobiusGroup.comp developingMap.holonomy.toMonoidHom

namespace HyperbolicInducedProjectiveStructure

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- Build the induced-projective-structure package from the atlas-construction package. -/
def ofProjectiveAtlasFromDevelopingMap
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}
    (A : ProjectiveAtlasFromDevelopingMap X D) :
    HyperbolicInducedProjectiveStructure X x₀ g where
  developingMap := D.hyperbolicDevelopingMap
  projectivizedDevelopingMap := D
  projectivized_developingMap_eq := rfl
  projectiveStructure := A.projectiveStructure
  projectiveHolonomy := A.projectiveHolonomy
  projectivized_holonomy_eq := A.projectiveHolonomy_eq.symm
  atlasFromDevelopingMap := A
  projectiveStructure_eq_atlas := rfl
  projectiveHolonomy_eq_atlas := rfl
  holonomy_matches_real_holonomy := A.projectiveHolonomy_eq_complexified_real

/-- Forget the hyperbolic provenance and keep the based projective surface. -/
def toBasedProjectiveSurface
    (P : HyperbolicInducedProjectiveStructure X x₀ g) :
    BasedProjectiveSurface X where
  basepoint := x₀
  projectiveStructure := P.projectiveStructure
  holonomy := P.projectiveHolonomy
  holonomy_constructed_from_projective_charts :=
    { developingData := {
        cover := P.projectivizedDevelopingMap.hyperbolicDevelopingMap.cover
        developingMap := P.projectivizedDevelopingMap.projectiveDev
        equivariant_representatives := by
          intro γ
          rcases P.projectivizedDevelopingMap.projective_equivariant γ with ⟨M, hM, hdev⟩
          refine ⟨M, ?_, hdev⟩
          simpa [P.projectivized_holonomy_eq] using hM }
      baseChart := P.atlasFromDevelopingMap.localChartAt x₀
      baseChart_mem := by
        simpa [P.projectiveStructure_eq_atlas] using
          P.atlasFromDevelopingMap.localChartAt_mem_atlas x₀
      basepoint_mem_baseChart := P.atlasFromDevelopingMap.developingAtlas.mem_chartAt_source x₀
      developingMap_locally_agrees_with_projective_charts := by
        intro y
        let x := P.projectivizedDevelopingMap.hyperbolicDevelopingMap.cover.projection y
        let C := P.atlasFromDevelopingMap.developingAtlas.chartAt x
        have hx : x ∈ C.chart.source :=
          P.atlasFromDevelopingMap.developingAtlas.mem_chartAt_source x
        let u :
            P.projectivizedDevelopingMap.hyperbolicDevelopingMap.cover.total :=
          C.lift ⟨x, hx⟩
        have hu_fiber :
            P.projectivizedDevelopingMap.hyperbolicDevelopingMap.cover.projection u =
              P.projectivizedDevelopingMap.hyperbolicDevelopingMap.cover.projection y := by
          simpa [u, x] using C.lift_projects ⟨x, hx⟩
        rcases
            P.projectivizedDevelopingMap.hyperbolicDevelopingMap.cover.deckAction_same_fiber_transitive
              u y hu_fiber with
          ⟨γ, hγ⟩
        rcases P.projectivizedDevelopingMap.projective_equivariant γ with
          ⟨M, _hM, hdev⟩
        exact ⟨{
          chart := C.chart
          chart_mem := by
            simpa [P.projectiveStructure_eq_atlas, C] using
              P.atlasFromDevelopingMap.localChartAt_mem_atlas x
          projected_mem := by
            simpa [x, C] using hx
          lift := fun z ↦
            P.projectivizedDevelopingMap.hyperbolicDevelopingMap.cover.deckAction γ
              (C.lift z)
          lift_projects := by
            intro z
            calc
              P.projectivizedDevelopingMap.hyperbolicDevelopingMap.cover.projection
                  (P.projectivizedDevelopingMap.hyperbolicDevelopingMap.cover.deckAction
                    γ (C.lift z)) =
                  P.projectivizedDevelopingMap.hyperbolicDevelopingMap.cover.projection
                    (C.lift z) := by
                exact
                  P.projectivizedDevelopingMap.hyperbolicDevelopingMap.cover.projection_deckAction
                    γ (C.lift z)
              _ = (z : X) := C.lift_projects z
          lift_through_y := by
            simpa [u, x, C] using hγ
          lift_continuous :=
            (P.projectivizedDevelopingMap.hyperbolicDevelopingMap.cover.deckTransformation
              γ).continuous.comp C.lift_continuous
          normalization := M
          developing_eq_normalized_chart := by
            intro z
            calc
              P.projectivizedDevelopingMap.projectiveDev
                  (P.projectivizedDevelopingMap.hyperbolicDevelopingMap.cover.deckAction
                    γ (C.lift z)) =
                  M • P.projectivizedDevelopingMap.projectiveDev (C.lift z) :=
                hdev (C.lift z)
              _ = M • C.chart (z : X) := by
                rw [C.chart_eq_projectiveDev z]
        }⟩
      transition_mobius := by
        intro e he e' he'
        have heA : e ∈ P.atlasFromDevelopingMap.projectiveStructure.atlasSet := by
          simpa [P.projectiveStructure_eq_atlas] using he
        have heA' : e' ∈ P.atlasFromDevelopingMap.projectiveStructure.atlasSet := by
          simpa [P.projectiveStructure_eq_atlas] using he'
        exact P.atlasFromDevelopingMap.projectiveStructure.transition_mobius_of_mem heA heA' }

/--
The holonomy of the induced projective structure is the complexification of the
real holonomy of its hyperbolic developing map.
-/
theorem projectiveHolonomy_eq_complexified_real
    (P : HyperbolicInducedProjectiveStructure X x₀ g) :
    P.projectiveHolonomy.toMonoidHom =
      realMobiusToMobiusGroup.comp P.developingMap.holonomy.toMonoidHom := by
  exact P.holonomy_matches_real_holonomy

/-- The stored atlas is the source of the stored projective structure. -/
theorem projectiveStructure_eq_atlasFromDevelopingMap
    (P : HyperbolicInducedProjectiveStructure X x₀ g) :
    P.projectiveStructure = P.atlasFromDevelopingMap.projectiveStructure :=
  P.projectiveStructure_eq_atlas

/-- The stored atlas is the source of the stored projective holonomy. -/
theorem projectiveHolonomy_eq_atlasFromDevelopingMap
    (P : HyperbolicInducedProjectiveStructure X x₀ g) :
    P.projectiveHolonomy = P.atlasFromDevelopingMap.projectiveHolonomy :=
  P.projectiveHolonomy_eq_atlas

/--
The induced projective structure has verified real holonomy in the strong
developing-atlas sense: the holonomy is attached to the stored atlas, not merely
some unrelated based representation.
-/
def verifiedRealHolonomyFromHyperbolicDevelopingAtlas
    (P : HyperbolicInducedProjectiveStructure X x₀ g) :
    P.projectiveStructure.VerifiedRealHolonomyFromHyperbolicDevelopingAtlas x₀ g :=
  { projectivizedDevelopingMap := P.projectivizedDevelopingMap
    atlasFromDevelopingMap := P.atlasFromDevelopingMap
    projectiveStructure_eq := P.projectiveStructure_eq_atlas.symm
    projectiveHolonomy_eq_complexified_real :=
      P.atlasFromDevelopingMap.projectiveHolonomy_eq_complexified_real }

/--
The holonomy of the induced projective structure has identity Mobius
normalization into `PSL(2, ℝ)`.
-/
def projectiveHolonomyMobiusNormalization
    (P : HyperbolicInducedProjectiveStructure X x₀ g) :
    ProjectiveHolonomyMobiusNormalization x₀ P.projectiveHolonomy :=
  ProjectiveHolonomyMobiusNormalization.of_complexified_real
    P.developingMap.holonomy P.projectiveHolonomy
    P.projectiveHolonomy_eq_complexified_real

@[simp]
theorem projectiveHolonomyMobiusNormalization_postcomposition
    (P : HyperbolicInducedProjectiveStructure X x₀ g) :
    P.projectiveHolonomyMobiusNormalization.postcomposition = 1 :=
  rfl

/--
The normalized holonomy representation of the induced projective structure is
the complexification of its hyperbolic real holonomy.
-/
theorem projectiveHolonomyMobiusNormalization_normalizedHolonomyRepresentation_complexifies_real
    (P : HyperbolicInducedProjectiveStructure X x₀ g) :
    P.projectiveHolonomyMobiusNormalization.normalizedHolonomyRepresentation.IsComplexificationOfReal :=
  P.projectiveHolonomyMobiusNormalization.normalizedHolonomyRepresentation_isComplexificationOfReal

/-- The induced projective holonomy is conjugate into `PSL(2, ℝ)`. -/
theorem projectiveHolonomy_isConjugateIntoPSL2R
    (P : HyperbolicInducedProjectiveStructure X x₀ g) :
    P.projectiveHolonomy.IsConjugateIntoPSL2R :=
  ⟨P.projectiveHolonomyMobiusNormalization⟩

/--
The induced projective structure has literal `PSL(2, ℝ)` holonomy, certified by
the developing atlas constructed from the projectivized hyperbolic developing
map.
-/
theorem hasPSL2RHolonomy
    (P : HyperbolicInducedProjectiveStructure X x₀ g) :
    HasPSL2RHolonomy x₀ P.projectiveStructure := by
  rw [P.projectiveStructure_eq_atlas]
  exact P.atlasFromDevelopingMap.hasPSL2RHolonomy

/--
The induced projective structure satisfies the Mobius-postcomposition version
of real holonomy.
-/
theorem hasPSL2RHolonomyAfterMobiusPostcomposition
    (P : HyperbolicInducedProjectiveStructure X x₀ g) :
    HasPSL2RHolonomyAfterMobiusPostcomposition x₀ P.projectiveStructure :=
  ⟨{
    projectiveHolonomy := P.projectiveHolonomy
    holonomy_constructed_from_projective_charts :=
      P.toBasedProjectiveSurface.holonomy_constructed_from_projective_charts
    normalization := P.projectiveHolonomyMobiusNormalization
  }⟩

end HyperbolicInducedProjectiveStructure

namespace ComplexProjectiveStructure

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/--
%%handwave
name:
  Induced by a hyperbolic metric
statement:
  A complex projective structure is induced by a hyperbolic metric $g$ when it
  is the projective structure assembled from a projectivized hyperbolic
  developing map for $g$.
-/
def IsInducedByHyperbolicMetric (P : ComplexProjectiveStructure X)
    (g : HyperbolicMetric X) : Prop :=
  ∃ x₀ : X, ∃ D : ProjectivizedHyperbolicDevelopingMap X x₀ g,
    ∃ A : ProjectiveAtlasFromDevelopingMap X D,
      A.projectiveStructure = P

/-- The induced projective structure is induced by the metric used in its developing map. -/
theorem isInducedByHyperbolicMetric_of_hyperbolic_induced_projective_structure
    {x₀ : X} {g : HyperbolicMetric X}
    (P : HyperbolicInducedProjectiveStructure X x₀ g) :
    P.projectiveStructure.IsInducedByHyperbolicMetric g :=
  ⟨x₀, P.projectivizedDevelopingMap, P.atlasFromDevelopingMap,
    P.projectiveStructure_eq_atlas.symm⟩

/-- An inducing hyperbolic developing map gives an existential `PSL(2, ℝ)` holonomy certificate. -/
theorem exists_has_psl2r_holonomy_of_isInducedByHyperbolicMetric
    (P : ComplexProjectiveStructure X) {g : HyperbolicMetric X}
    (h : P.IsInducedByHyperbolicMetric g) :
    ∃ x₀ : X, HasPSL2RHolonomy x₀ P := by
  rcases h with ⟨x₀, _D, A, hA⟩
  refine ⟨x₀, ?_⟩
  rw [← hA]
  exact A.hasPSL2RHolonomy

end ComplexProjectiveStructure

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/--
%%handwave
name:
  Real projective structure induced by a metric
statement:
  A hyperbolic metric induces a real projective structure at a basepoint when
  there is a concrete hyperbolic-induced projective-structure package for that
  basepoint and metric.
-/
def InducesRealProjectiveStructure (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (HyperbolicInducedProjectiveStructure X x₀ g)

/--
Metric-bound public endpoint: the projective structure with real holonomy is
the one induced by the given hyperbolic metric.
-/
def DefinesInducedProjectiveStructureWithPSL2RHolonomy (x₀ : X)
    (g : HyperbolicMetric X) : Prop :=
  g.InducesRealProjectiveStructure x₀

/--
Weak metric-free endpoint: the surface admits some complex projective
structure whose holonomy is certified to factor through `PSL(2, ℝ)`.
-/
def ExistsProjectiveStructureWithPSL2RHolonomy (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] (x₀ : X) : Prop :=
  ∃ P : ComplexProjectiveStructure X, HasPSL2RHolonomy x₀ P

/--
%%handwave
name:
  Defines a $\mathrm{PSL}_2(\mathbb R)$ projective structure
statement:
  The public metric-bound endpoint says that the hyperbolic metric defines its
  induced complex projective structure and that the holonomy is certified to
  factor through $\mathrm{PSL}_2(\mathbb R)$.
-/
def DefinesProjectiveStructureWithPSL2RHolonomy (x₀ : X)
    (g : HyperbolicMetric X) : Prop :=
  g.InducesRealProjectiveStructure x₀

/--
Target package: a projectivized developing map has been used to construct the
projective atlas on `X`.
-/
def HasProjectiveAtlasFromDevelopingMap (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  ∃ D : ProjectivizedHyperbolicDevelopingMap X x₀ g,
    Nonempty (ProjectiveAtlasFromDevelopingMap X D)

theorem inducesRealProjectiveStructure_of_hasProjectiveAtlasFromDevelopingMap
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasFromDevelopingMap x₀) :
    g.InducesRealProjectiveStructure x₀ := by
  rcases h with ⟨D, ⟨A⟩⟩
  exact ⟨HyperbolicInducedProjectiveStructure.ofProjectiveAtlasFromDevelopingMap A⟩

/-- The induced-structure package implies the metric-bound public PSL-holonomy endpoint. -/
theorem definesProjectiveStructureWithPSL2RHolonomy_of_induced
    {x₀ : X} {g : HyperbolicMetric X}
    (P : HyperbolicInducedProjectiveStructure X x₀ g) :
    g.DefinesProjectiveStructureWithPSL2RHolonomy x₀ :=
  ⟨P⟩

/-- The induced-structure package implies the weak metric-free PSL endpoint. -/
theorem existsProjectiveStructureWithPSL2RHolonomy_of_induced
    {x₀ : X} {g : HyperbolicMetric X}
    (P : HyperbolicInducedProjectiveStructure X x₀ g) :
    ExistsProjectiveStructureWithPSL2RHolonomy X x₀ :=
  ⟨P.projectiveStructure, P.hasPSL2RHolonomy⟩

/-- The packaged real-projective-structure endpoint implies the metric-bound public endpoint. -/
theorem definesProjectiveStructureWithPSL2RHolonomy_of_inducesRealProjectiveStructure
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.InducesRealProjectiveStructure x₀) :
    g.DefinesProjectiveStructureWithPSL2RHolonomy x₀ :=
  h

/-- The packaged real-projective-structure endpoint implies the weak metric-free endpoint. -/
theorem existsProjectiveStructureWithPSL2RHolonomy_of_inducesRealProjectiveStructure
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.InducesRealProjectiveStructure x₀) :
    ExistsProjectiveStructureWithPSL2RHolonomy X x₀ := by
  rcases h with ⟨P⟩
  exact existsProjectiveStructureWithPSL2RHolonomy_of_induced P

/-- The metric-bound endpoint is definitionally the induced-structure package. -/
theorem definesInducedProjectiveStructureWithPSL2RHolonomy_iff
    {x₀ : X} {g : HyperbolicMetric X} :
    g.DefinesInducedProjectiveStructureWithPSL2RHolonomy x₀ ↔
      g.InducesRealProjectiveStructure x₀ :=
  Iff.rfl

/-- The public PSL endpoint is also definitionally the induced-structure package. -/
theorem definesProjectiveStructureWithPSL2RHolonomy_iff
    {x₀ : X} {g : HyperbolicMetric X} :
    g.DefinesProjectiveStructureWithPSL2RHolonomy x₀ ↔
      g.InducesRealProjectiveStructure x₀ :=
  Iff.rfl

/-- The compatibility metric-bound endpoint implies the public PSL endpoint. -/
theorem definesProjectiveStructureWithPSL2RHolonomy_of_definesInducedProjectiveStructureWithPSL2RHolonomy
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.DefinesInducedProjectiveStructureWithPSL2RHolonomy x₀) :
    g.DefinesProjectiveStructureWithPSL2RHolonomy x₀ :=
  h

/-- The metric-bound public endpoint implies the weak metric-free PSL endpoint. -/
theorem existsProjectiveStructureWithPSL2RHolonomy_of_definesProjectiveStructureWithPSL2RHolonomy
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.DefinesProjectiveStructureWithPSL2RHolonomy x₀) :
    ExistsProjectiveStructureWithPSL2RHolonomy X x₀ :=
  existsProjectiveStructureWithPSL2RHolonomy_of_inducesRealProjectiveStructure h

theorem admitsProjectivizedDevelopingMap_of_hasProjectiveAtlasFromDevelopingMap
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasFromDevelopingMap x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ := by
  rcases h with ⟨D, _⟩
  exact ⟨D⟩

theorem admitsDevelopingMap_of_hasProjectiveAtlasFromDevelopingMap
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasFromDevelopingMap x₀) :
    g.AdmitsDevelopingMap x₀ := by
  rcases h with ⟨D, _⟩
  exact ⟨D.hyperbolicDevelopingMap⟩

/--
Pipeline-specific atlas package: the hyperbolic developing pipeline is fixed,
and the projective atlas is constructed from the projectivized developing map
produced by that same pipeline.
-/
structure HasProjectiveAtlasForDevelopingPipeline (x₀ : X) (g : HyperbolicMetric X) where
  /-- The local-to-global hyperbolic developing pipeline. -/
  developingPipeline : HyperbolicDevelopingPipeline X x₀ g
  /-- The projective atlas built from the projectivized developing map of this pipeline. -/
  atlasFromDevelopingMap :
    ProjectiveAtlasFromDevelopingMap X
      developingPipeline.toProjectivizedDevelopingMap

theorem hasDevelopingPipeline_of_hasProjectiveAtlasForDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingPipeline x₀) :
    g.HasDevelopingPipeline x₀ :=
  ⟨h.developingPipeline⟩

theorem hasProjectiveAtlasFromDevelopingMap_of_hasProjectiveAtlasForDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingPipeline x₀) :
    g.HasProjectiveAtlasFromDevelopingMap x₀ :=
  ⟨h.developingPipeline.toProjectivizedDevelopingMap, ⟨h.atlasFromDevelopingMap⟩⟩

theorem admitsProjectivizedDevelopingMap_of_hasProjectiveAtlasForDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingPipeline x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  ⟨h.developingPipeline.toProjectivizedDevelopingMap⟩

/--
Construction-pipeline-specific atlas package: the refined hyperbolic developing
pipeline is fixed, and the projective atlas is built from the projectivized
developing map produced by its underlying developing pipeline.
-/
structure HasProjectiveAtlasForDevelopingConstructionPipeline
    (x₀ : X) (g : HyperbolicMetric X) where
  /-- The refined local-to-global hyperbolic developing pipeline. -/
  developingConstructionPipeline : HyperbolicDevelopingConstructionPipeline X x₀ g
  /-- The projective atlas built from the projectivized developing map of this pipeline. -/
  atlasFromDevelopingMap :
    ProjectiveAtlasFromDevelopingMap X
      developingConstructionPipeline.toHyperbolicDevelopingPipeline.toProjectivizedDevelopingMap

def hasProjectiveAtlasForDevelopingPipeline_of_hasProjectiveAtlasForDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingConstructionPipeline x₀) :
    g.HasProjectiveAtlasForDevelopingPipeline x₀ where
  developingPipeline := h.developingConstructionPipeline.toHyperbolicDevelopingPipeline
  atlasFromDevelopingMap := h.atlasFromDevelopingMap

theorem hasDevelopingConstructionPipeline_of_hasProjectiveAtlasForDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingConstructionPipeline x₀) :
    g.HasDevelopingConstructionPipeline x₀ :=
  ⟨h.developingConstructionPipeline⟩

theorem hasDevelopingPipeline_of_hasProjectiveAtlasForDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingConstructionPipeline x₀) :
    g.HasDevelopingPipeline x₀ :=
  hasDevelopingPipeline_of_hasDevelopingConstructionPipeline
    (hasDevelopingConstructionPipeline_of_hasProjectiveAtlasForDevelopingConstructionPipeline h)

theorem hasProjectiveAtlasFromDevelopingMap_of_hasProjectiveAtlasForDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingConstructionPipeline x₀) :
    g.HasProjectiveAtlasFromDevelopingMap x₀ :=
  hasProjectiveAtlasFromDevelopingMap_of_hasProjectiveAtlasForDevelopingPipeline
    (hasProjectiveAtlasForDevelopingPipeline_of_hasProjectiveAtlasForDevelopingConstructionPipeline h)

theorem admitsProjectivizedDevelopingMap_of_hasProjectiveAtlasForDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingConstructionPipeline x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  admitsProjectivizedDevelopingMap_of_hasProjectiveAtlasForDevelopingPipeline
    (hasProjectiveAtlasForDevelopingPipeline_of_hasProjectiveAtlasForDevelopingConstructionPipeline h)

/--
Curvature-pipeline-specific atlas package: the curvature-aware hyperbolic
developing pipeline is fixed, and the projective atlas is built from the
projectivized developing map produced by its underlying developing pipeline.
-/
structure HasProjectiveAtlasForDevelopingCurvaturePipeline
    (x₀ : X) (g : HyperbolicMetric X) where
  /-- The curvature-aware local-to-global hyperbolic developing pipeline. -/
  developingCurvaturePipeline : HyperbolicDevelopingCurvaturePipeline X x₀ g
  /-- The projective atlas built from the projectivized developing map of this pipeline. -/
  atlasFromDevelopingMap :
    ProjectiveAtlasFromDevelopingMap X
      developingCurvaturePipeline.toProjectivizedDevelopingMap

def hasProjectiveAtlasForDevelopingConstructionPipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.HasProjectiveAtlasForDevelopingConstructionPipeline x₀ where
  developingConstructionPipeline :=
    h.developingCurvaturePipeline.toHyperbolicDevelopingConstructionPipeline
  atlasFromDevelopingMap := h.atlasFromDevelopingMap

theorem hasDevelopingCurvaturePipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.HasDevelopingCurvaturePipeline x₀ :=
  ⟨h.developingCurvaturePipeline⟩

theorem hasDevelopingConstructionPipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.HasDevelopingConstructionPipeline x₀ :=
  hasDevelopingConstructionPipeline_of_hasDevelopingCurvaturePipeline
    (hasDevelopingCurvaturePipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline h)

theorem hasProjectiveAtlasFromDevelopingMap_of_hasProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.HasProjectiveAtlasFromDevelopingMap x₀ :=
  hasProjectiveAtlasFromDevelopingMap_of_hasProjectiveAtlasForDevelopingConstructionPipeline
    (hasProjectiveAtlasForDevelopingConstructionPipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline h)

theorem admitsProjectivizedDevelopingMap_of_hasProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  admitsProjectivizedDevelopingMap_of_hasProjectiveAtlasForDevelopingConstructionPipeline
    (hasProjectiveAtlasForDevelopingConstructionPipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline h)

/-- The projectivized developing map used by the curvature-pipeline atlas package. -/
def projectivizedDevelopingMapOfCurvatureAtlasPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    ProjectivizedHyperbolicDevelopingMap X x₀ g :=
  h.developingCurvaturePipeline.toProjectivizedDevelopingMap

/-- The projective atlas constructed in the curvature-pipeline package. -/
def projectiveAtlasOfCurvatureAtlasPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    ProjectiveAtlasFromDevelopingMap X
      (projectivizedDevelopingMapOfCurvatureAtlasPipeline h) :=
  h.atlasFromDevelopingMap

@[simp]
theorem projectivizedDevelopingMapOfCurvatureAtlasPipeline_hyperbolicDevelopingMap
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    (projectivizedDevelopingMapOfCurvatureAtlasPipeline h).hyperbolicDevelopingMap =
      h.developingCurvaturePipeline.toHyperbolicDevelopingMap :=
  rfl

/-- The projectivized developing map used by the construction-pipeline atlas package. -/
def projectivizedDevelopingMapOfConstructionAtlasPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingConstructionPipeline x₀) :
    ProjectivizedHyperbolicDevelopingMap X x₀ g :=
  h.developingConstructionPipeline.toProjectivizedDevelopingMap

/-- The projective atlas constructed in the construction-pipeline package. -/
def projectiveAtlasOfConstructionAtlasPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingConstructionPipeline x₀) :
    ProjectiveAtlasFromDevelopingMap X
      (projectivizedDevelopingMapOfConstructionAtlasPipeline h) :=
  h.atlasFromDevelopingMap

@[simp]
theorem projectivizedDevelopingMapOfConstructionAtlasPipeline_hyperbolicDevelopingMap
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingConstructionPipeline x₀) :
    (projectivizedDevelopingMapOfConstructionAtlasPipeline h).hyperbolicDevelopingMap =
      h.developingConstructionPipeline.toHyperbolicDevelopingMap :=
  rfl

/-- The projectivized developing map used by the pipeline-specific atlas package. -/
def projectivizedDevelopingMapOfAtlasPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingPipeline x₀) :
    ProjectivizedHyperbolicDevelopingMap X x₀ g :=
  h.developingPipeline.toProjectivizedDevelopingMap

/-- The projective atlas constructed in the pipeline-specific package. -/
def projectiveAtlasOfAtlasPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingPipeline x₀) :
    ProjectiveAtlasFromDevelopingMap X
      (projectivizedDevelopingMapOfAtlasPipeline h) :=
  h.atlasFromDevelopingMap

@[simp]
theorem projectivizedDevelopingMapOfAtlasPipeline_hyperbolicDevelopingMap
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingPipeline x₀) :
    (projectivizedDevelopingMapOfAtlasPipeline h).hyperbolicDevelopingMap =
      h.developingPipeline.toHyperbolicDevelopingMap :=
  rfl

/--
Strong projectivization package: the developing pipeline has been used to build
the induced complex projective structure.
-/
structure HasProjectivizedDevelopingPipeline (x₀ : X) (g : HyperbolicMetric X) where
  /-- The local-to-global hyperbolic developing pipeline. -/
  developingPipeline : HyperbolicDevelopingPipeline X x₀ g
  /-- The induced projective-structure output. -/
  inducedProjectiveStructure : HyperbolicInducedProjectiveStructure X x₀ g
  /-- The projective output uses the developing map produced by the pipeline. -/
  projectivizes_pipeline :
    inducedProjectiveStructure.developingMap =
      developingPipeline.toHyperbolicDevelopingMap

/--
Curvature-aware strong projectivization package: the curvature-derived
developing pipeline has been used to build the induced complex projective
structure.
-/
structure HasCurvatureProjectivizedDevelopingPipeline
    (x₀ : X) (g : HyperbolicMetric X) where
  /-- The curvature-aware local-to-global hyperbolic developing pipeline. -/
  developingCurvaturePipeline : HyperbolicDevelopingCurvaturePipeline X x₀ g
  /-- The induced projective-structure output. -/
  inducedProjectiveStructure : HyperbolicInducedProjectiveStructure X x₀ g
  /-- The projective output uses the developing map produced by the curvature pipeline. -/
  projectivizes_curvature_pipeline :
    inducedProjectiveStructure.developingMap =
      developingCurvaturePipeline.toHyperbolicDevelopingMap

theorem inducesRealProjectiveStructure_of_hasProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectivizedDevelopingPipeline x₀) :
    g.InducesRealProjectiveStructure x₀ :=
  ⟨h.inducedProjectiveStructure⟩

def hasProjectivizedDevelopingPipeline_of_hasCurvatureProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasCurvatureProjectivizedDevelopingPipeline x₀) :
    g.HasProjectivizedDevelopingPipeline x₀ where
  developingPipeline := h.developingCurvaturePipeline.toHyperbolicDevelopingPipeline
  inducedProjectiveStructure := h.inducedProjectiveStructure
  projectivizes_pipeline := h.projectivizes_curvature_pipeline

theorem hasDevelopingCurvaturePipeline_of_hasCurvatureProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasCurvatureProjectivizedDevelopingPipeline x₀) :
    g.HasDevelopingCurvaturePipeline x₀ :=
  ⟨h.developingCurvaturePipeline⟩

theorem inducesRealProjectiveStructure_of_hasCurvatureProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasCurvatureProjectivizedDevelopingPipeline x₀) :
    g.InducesRealProjectiveStructure x₀ :=
  ⟨h.inducedProjectiveStructure⟩

def hasProjectivizedDevelopingPipeline_of_hasProjectiveAtlasForDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingPipeline x₀) :
    g.HasProjectivizedDevelopingPipeline x₀ where
  developingPipeline := h.developingPipeline
  inducedProjectiveStructure :=
    HyperbolicInducedProjectiveStructure.ofProjectiveAtlasFromDevelopingMap
      h.atlasFromDevelopingMap
  projectivizes_pipeline := rfl

def hasCurvatureProjectivizedDevelopingPipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.HasCurvatureProjectivizedDevelopingPipeline x₀ where
  developingCurvaturePipeline := h.developingCurvaturePipeline
  inducedProjectiveStructure :=
    HyperbolicInducedProjectiveStructure.ofProjectiveAtlasFromDevelopingMap
      h.atlasFromDevelopingMap
  projectivizes_curvature_pipeline := rfl

theorem inducesRealProjectiveStructure_of_hasProjectiveAtlasForDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingPipeline x₀) :
    g.InducesRealProjectiveStructure x₀ :=
  inducesRealProjectiveStructure_of_hasProjectivizedDevelopingPipeline
    (hasProjectivizedDevelopingPipeline_of_hasProjectiveAtlasForDevelopingPipeline h)

theorem admitsDevelopingMap_of_hasProjectiveAtlasForDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingPipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasProjectiveAtlasForDevelopingPipeline h)

theorem inducesRealProjectiveStructure_of_hasProjectiveAtlasForDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingConstructionPipeline x₀) :
    g.InducesRealProjectiveStructure x₀ :=
  inducesRealProjectiveStructure_of_hasProjectiveAtlasForDevelopingPipeline
    (hasProjectiveAtlasForDevelopingPipeline_of_hasProjectiveAtlasForDevelopingConstructionPipeline h)

theorem admitsDevelopingMap_of_hasProjectiveAtlasForDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingConstructionPipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_hasProjectiveAtlasForDevelopingPipeline
    (hasProjectiveAtlasForDevelopingPipeline_of_hasProjectiveAtlasForDevelopingConstructionPipeline h)

theorem inducesRealProjectiveStructure_of_hasProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.InducesRealProjectiveStructure x₀ :=
  inducesRealProjectiveStructure_of_hasProjectiveAtlasForDevelopingConstructionPipeline
    (hasProjectiveAtlasForDevelopingConstructionPipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline h)

theorem admitsDevelopingMap_of_hasProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_hasProjectiveAtlasForDevelopingConstructionPipeline
    (hasProjectiveAtlasForDevelopingConstructionPipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline h)

theorem hasDevelopingPipeline_of_hasProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectivizedDevelopingPipeline x₀) :
    g.HasDevelopingPipeline x₀ :=
  ⟨h.developingPipeline⟩

theorem admitsProjectivizedDevelopingMap_of_hasProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectivizedDevelopingPipeline x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  admitsProjectivizedDevelopingMap_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasProjectivizedDevelopingPipeline h)

theorem admitsDevelopingMap_of_hasProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectivizedDevelopingPipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasProjectivizedDevelopingPipeline h)

theorem hasDevelopingPipeline_of_hasCurvatureProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasCurvatureProjectivizedDevelopingPipeline x₀) :
    g.HasDevelopingPipeline x₀ :=
  hasDevelopingPipeline_of_hasProjectivizedDevelopingPipeline
    (hasProjectivizedDevelopingPipeline_of_hasCurvatureProjectivizedDevelopingPipeline h)

theorem admitsProjectivizedDevelopingMap_of_hasCurvatureProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasCurvatureProjectivizedDevelopingPipeline x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  admitsProjectivizedDevelopingMap_of_hasProjectivizedDevelopingPipeline
    (hasProjectivizedDevelopingPipeline_of_hasCurvatureProjectivizedDevelopingPipeline h)

theorem admitsDevelopingMap_of_hasCurvatureProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasCurvatureProjectivizedDevelopingPipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_hasProjectivizedDevelopingPipeline
    (hasProjectivizedDevelopingPipeline_of_hasCurvatureProjectivizedDevelopingPipeline h)

/--
Prop-level target: the projective atlas has been constructed from the
projectivized developing map produced by a fixed developing pipeline.
-/
def AdmitsProjectiveAtlasForDevelopingPipeline
    (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (g.HasProjectiveAtlasForDevelopingPipeline x₀)

/--
Prop-level target: the projective atlas has been constructed from the
projectivized developing map produced by a fixed construction-level pipeline.
-/
def AdmitsProjectiveAtlasForDevelopingConstructionPipeline
    (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (g.HasProjectiveAtlasForDevelopingConstructionPipeline x₀)

/--
Prop-level target: the projective atlas has been constructed from the
projectivized developing map produced by a fixed curvature-aware pipeline.
-/
def AdmitsProjectiveAtlasForDevelopingCurvaturePipeline
    (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀)

/--
Prop-level target: the developing pipeline has been projectivized into an
induced complex projective structure.
-/
def AdmitsProjectivizedDevelopingPipeline
    (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (g.HasProjectivizedDevelopingPipeline x₀)

/--
Prop-level target: the curvature-aware developing pipeline has been
projectivized into an induced complex projective structure.
-/
def AdmitsCurvatureProjectivizedDevelopingPipeline
    (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (g.HasCurvatureProjectivizedDevelopingPipeline x₀)

theorem admitsProjectiveAtlasForDevelopingPipeline_of_hasProjectiveAtlasForDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingPipeline x₀) :
    g.AdmitsProjectiveAtlasForDevelopingPipeline x₀ :=
  ⟨h⟩

theorem admitsProjectiveAtlasForDevelopingConstructionPipeline_of_hasProjectiveAtlasForDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingConstructionPipeline x₀) :
    g.AdmitsProjectiveAtlasForDevelopingConstructionPipeline x₀ :=
  ⟨h⟩

theorem admitsProjectiveAtlasForDevelopingCurvaturePipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.AdmitsProjectiveAtlasForDevelopingCurvaturePipeline x₀ :=
  ⟨h⟩

theorem admitsProjectivizedDevelopingPipeline_of_hasProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectivizedDevelopingPipeline x₀) :
    g.AdmitsProjectivizedDevelopingPipeline x₀ :=
  ⟨h⟩

theorem admitsCurvatureProjectivizedDevelopingPipeline_of_hasCurvatureProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasCurvatureProjectivizedDevelopingPipeline x₀) :
    g.AdmitsCurvatureProjectivizedDevelopingPipeline x₀ :=
  ⟨h⟩

theorem admitsProjectiveAtlasForDevelopingPipeline_of_admitsProjectiveAtlasForDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingConstructionPipeline x₀) :
    g.AdmitsProjectiveAtlasForDevelopingPipeline x₀ :=
  h.elim fun H ↦
    ⟨hasProjectiveAtlasForDevelopingPipeline_of_hasProjectiveAtlasForDevelopingConstructionPipeline H⟩

theorem admitsProjectiveAtlasForDevelopingConstructionPipeline_of_admitsProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.AdmitsProjectiveAtlasForDevelopingConstructionPipeline x₀ :=
  h.elim fun H ↦
    ⟨hasProjectiveAtlasForDevelopingConstructionPipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline H⟩

theorem admitsProjectiveAtlasForDevelopingPipeline_of_admitsProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.AdmitsProjectiveAtlasForDevelopingPipeline x₀ :=
  admitsProjectiveAtlasForDevelopingPipeline_of_admitsProjectiveAtlasForDevelopingConstructionPipeline
    (admitsProjectiveAtlasForDevelopingConstructionPipeline_of_admitsProjectiveAtlasForDevelopingCurvaturePipeline h)

theorem admitsProjectivizedDevelopingPipeline_of_admitsCurvatureProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsCurvatureProjectivizedDevelopingPipeline x₀) :
    g.AdmitsProjectivizedDevelopingPipeline x₀ :=
  h.elim fun H ↦
    ⟨hasProjectivizedDevelopingPipeline_of_hasCurvatureProjectivizedDevelopingPipeline H⟩

theorem admitsProjectivizedDevelopingPipeline_of_admitsProjectiveAtlasForDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingPipeline x₀) :
    g.AdmitsProjectivizedDevelopingPipeline x₀ :=
  h.elim fun H ↦
    ⟨hasProjectivizedDevelopingPipeline_of_hasProjectiveAtlasForDevelopingPipeline H⟩

theorem admitsCurvatureProjectivizedDevelopingPipeline_of_admitsProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.AdmitsCurvatureProjectivizedDevelopingPipeline x₀ :=
  h.elim fun H ↦
    ⟨hasCurvatureProjectivizedDevelopingPipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline H⟩

theorem hasProjectiveAtlasFromDevelopingMap_of_admitsProjectiveAtlasForDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingPipeline x₀) :
    g.HasProjectiveAtlasFromDevelopingMap x₀ :=
  h.elim fun H ↦
    hasProjectiveAtlasFromDevelopingMap_of_hasProjectiveAtlasForDevelopingPipeline H

theorem hasProjectiveAtlasFromDevelopingMap_of_admitsProjectiveAtlasForDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingConstructionPipeline x₀) :
    g.HasProjectiveAtlasFromDevelopingMap x₀ :=
  hasProjectiveAtlasFromDevelopingMap_of_admitsProjectiveAtlasForDevelopingPipeline
    (admitsProjectiveAtlasForDevelopingPipeline_of_admitsProjectiveAtlasForDevelopingConstructionPipeline h)

theorem hasProjectiveAtlasFromDevelopingMap_of_admitsProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.HasProjectiveAtlasFromDevelopingMap x₀ :=
  hasProjectiveAtlasFromDevelopingMap_of_admitsProjectiveAtlasForDevelopingPipeline
    (admitsProjectiveAtlasForDevelopingPipeline_of_admitsProjectiveAtlasForDevelopingCurvaturePipeline h)

theorem inducesRealProjectiveStructure_of_admitsProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectivizedDevelopingPipeline x₀) :
    g.InducesRealProjectiveStructure x₀ :=
  h.elim fun H ↦ inducesRealProjectiveStructure_of_hasProjectivizedDevelopingPipeline H

theorem inducesRealProjectiveStructure_of_admitsCurvatureProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsCurvatureProjectivizedDevelopingPipeline x₀) :
    g.InducesRealProjectiveStructure x₀ :=
  h.elim fun H ↦
    inducesRealProjectiveStructure_of_hasCurvatureProjectivizedDevelopingPipeline H

theorem admitsProjectivizedDevelopingMap_of_admitsProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectivizedDevelopingPipeline x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  h.elim fun H ↦ admitsProjectivizedDevelopingMap_of_hasProjectivizedDevelopingPipeline H

theorem admitsProjectivizedDevelopingMap_of_admitsCurvatureProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsCurvatureProjectivizedDevelopingPipeline x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  h.elim fun H ↦
    admitsProjectivizedDevelopingMap_of_hasCurvatureProjectivizedDevelopingPipeline H

theorem admitsDevelopingMap_of_admitsProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectivizedDevelopingPipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  h.elim fun H ↦ admitsDevelopingMap_of_hasProjectivizedDevelopingPipeline H

theorem admitsDevelopingMap_of_admitsCurvatureProjectivizedDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsCurvatureProjectivizedDevelopingPipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  h.elim fun H ↦ admitsDevelopingMap_of_hasCurvatureProjectivizedDevelopingPipeline H

theorem admitsProjectivizedDevelopingMap_of_admitsProjectiveAtlasForDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingPipeline x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  admitsProjectivizedDevelopingMap_of_admitsProjectivizedDevelopingPipeline
    (admitsProjectivizedDevelopingPipeline_of_admitsProjectiveAtlasForDevelopingPipeline h)

theorem admitsProjectivizedDevelopingMap_of_admitsProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  admitsProjectivizedDevelopingMap_of_admitsCurvatureProjectivizedDevelopingPipeline
    (admitsCurvatureProjectivizedDevelopingPipeline_of_admitsProjectiveAtlasForDevelopingCurvaturePipeline h)

theorem admitsDevelopingMap_of_admitsProjectiveAtlasForDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingPipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_admitsProjectivizedDevelopingPipeline
    (admitsProjectivizedDevelopingPipeline_of_admitsProjectiveAtlasForDevelopingPipeline h)

theorem admitsDevelopingMap_of_admitsProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_admitsCurvatureProjectivizedDevelopingPipeline
    (admitsCurvatureProjectivizedDevelopingPipeline_of_admitsProjectiveAtlasForDevelopingCurvaturePipeline h)

theorem inducesRealProjectiveStructure_of_admitsProjectiveAtlasForDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingPipeline x₀) :
    g.InducesRealProjectiveStructure x₀ :=
  inducesRealProjectiveStructure_of_admitsProjectivizedDevelopingPipeline
    (admitsProjectivizedDevelopingPipeline_of_admitsProjectiveAtlasForDevelopingPipeline h)

theorem inducesRealProjectiveStructure_of_admitsProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.InducesRealProjectiveStructure x₀ :=
  inducesRealProjectiveStructure_of_admitsCurvatureProjectivizedDevelopingPipeline
    (admitsCurvatureProjectivizedDevelopingPipeline_of_admitsProjectiveAtlasForDevelopingCurvaturePipeline h)

end HyperbolicMetric

end

end JJMath
