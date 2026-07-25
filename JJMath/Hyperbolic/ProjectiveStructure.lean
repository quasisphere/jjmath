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

/-- The inclusion of the upper half-plane into the Riemann sphere.
%%handwave
name:
  Inclusion of the upper half-plane in the projective line
statement:
  The standard inclusion $\iota:\mathbb H\hookrightarrow\mathbb{CP}^1$ sends $z$ to the finite projective point represented by the same complex number.
-/
def upperHalfPlaneToRiemannSphere (z : ℍ) : RiemannSphere :=
  ((z : ℂ) : RiemannSphere)

/--
%%handwave
name:
  Evaluation of the upper-half-plane inclusion
statement:
  For every $z\in\mathbb H$, the standard inclusion $\iota:\mathbb H\hookrightarrow\mathbb{CP}^1$ sends $z$ to the finite projective point represented by the same complex number $z$.
proof:
  Unfolding the standard inclusion identifies both sides with the same finite point of $\mathbb{CP}^1$.
-/
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

/-- The projective developing map obtained by composing `dev : X̃ → ℍ` with `ℍ ⊂ ℂP¹`.
%%handwave
name:
  Projectivization of a hyperbolic developing map
statement:
  A hyperbolic developing map $\mathrm{dev}:\widetilde X\to\mathbb H$ determines the projective developing map $\iota\circ\mathrm{dev}:\widetilde X\to\mathbb{CP}^1$.
-/
def projectiveDev (D : HyperbolicDevelopingMap X x₀ g) :
    D.cover.total → RiemannSphere :=
  fun y ↦ upperHalfPlaneToRiemannSphere (D.dev y)

/-- The complex projective holonomy obtained by complexifying real hyperbolic holonomy.
%%handwave
name:
  Complexified projective holonomy
statement:
  The projective holonomy associated to $\rho:\pi_1(X,x_0)\to\mathrm{PSL}_2(\mathbb R)$ is its scalar extension $\iota_*\rho:\pi_1(X,x_0)\to\mathrm{PGL}_2(\mathbb C)$.
-/
def projectiveHolonomy (D : HyperbolicDevelopingMap X x₀ g) :
    HolonomyRepresentation X x₀ where
  toMonoidHom := realMobiusToMobiusGroup.comp D.holonomy.toMonoidHom

/-- A projective holonomy representation is the complexification of real hyperbolic holonomy.
%%handwave
name:
  Projective holonomy complexifies real holonomy
statement:
  For a hyperbolic developing map with real holonomy $\rho$, a projective holonomy $\widehat\rho$ complexifies it when $\widehat\rho=\iota_*\rho$ as representations of $\pi_1(X,x_0)$.
-/
def ProjectiveHolonomyComplexifiesReal (D : HyperbolicDevelopingMap X x₀ g)
    (ρ : HolonomyRepresentation X x₀) : Prop :=
  ρ.toMonoidHom = realMobiusToMobiusGroup.comp D.holonomy.toMonoidHom

/--
Projective equivariance of the composed developing map, stated with explicit
`GL(2, ℂ)` representatives of projective holonomy.

This avoids needing a global `PGL(2, ℂ)` action on the Riemann sphere: for each
loop, a representative of the projective holonomy sends the projective
coordinate of every `y` to that of its deck translate.

%%handwave
name:
  Equivariance of a projective developing map
statement:
  A projectivized developing map is equivariant for $\widehat\rho$ when, for every $\gamma\in\pi_1(X,x_0)$, a matrix representing $\widehat\rho(\gamma)$ carries $\mathrm{dev}(y)$ to $\mathrm{dev}(\gamma\cdot y)$ for every $y\in\widetilde X$.
-/
def ProjectiveEquivariant (D : HyperbolicDevelopingMap X x₀ g)
    (ρ : HolonomyRepresentation X x₀) : Prop :=
  ∀ γ, ∃ A : MobiusRepresentative,
    Matrix.ProjGenLinGroup.mk A = ρ γ ∧
      ∀ y, D.projectiveDev (D.cover.deckAction γ y) = A • D.projectiveDev y

/--
%%handwave
name:
  Projective holonomy is the complexification of real holonomy
statement:
  For every hyperbolic developing map $D$, its projective holonomy is the scalar extension of its real holonomy $\rho:\pi_1(X,x_0)\to\mathrm{PSL}_2(\mathbb R)$ to $\mathrm{PGL}_2(\mathbb C)$.
proof:
  The complexification condition is precisely the equality used to define the projective holonomy.
-/
@[simp]
theorem projectiveHolonomy_complexifies_real (D : HyperbolicDevelopingMap X x₀ g) :
    D.ProjectiveHolonomyComplexifiesReal D.projectiveHolonomy :=
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

/-- Projectivization preserves the strengthened finite-coordinate regularity.
%%handwave
name:
  Finite-coordinate regularity after projectivization
statement:
  Let $D:\widetilde X_{x_0}\to\mathbb H$ be a regular hyperbolic developing map. At every $y\in\widetilde X_{x_0}$, the finite complex-coordinate expression of $\iota\circ D$ equals that of $D$.
proof:
  At each cover point $y$, projectivization leaves the finite complex coordinate expression unchanged, so the required equality is reflexive.
-/
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

/-- The Riemann-sphere-valued developing map underlying a projectivized package.
%%handwave
name:
  Developing map underlying a projectivized hyperbolic package
statement:
  The projective developing map underlying a projectivized hyperbolic developing package is the composition of its hyperbolic developing map with $\mathbb H\hookrightarrow\mathbb{CP}^1$.
-/
def projectiveDev (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) :
    D.hyperbolicDevelopingMap.cover.total → RiemannSphere :=
  D.hyperbolicDevelopingMap.projectiveDev

/-- The projective holonomy of a projectivized developing map is the complexified real holonomy.
%%handwave
name:
  The projective holonomy of a projectivized developing map is the complexified real holonomy
statement:
  The projective holonomy of a projectivized developing map is the complexified real holonomy.
proof:
  Use the stored equality identifying the projective holonomy with the complexification of the hyperbolic real holonomy.
-/
theorem projectiveHolonomy_eq_complexified_real
    (D : ProjectivizedHyperbolicDevelopingMap X x₀ g) :
    D.projectiveHolonomy.toMonoidHom =
      realMobiusToMobiusGroup.comp D.hyperbolicDevelopingMap.holonomy.toMonoidHom :=
  D.projectiveHolonomy_complexifies_real

end ProjectivizedHyperbolicDevelopingMap

namespace HyperbolicDevelopingMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/--
Projectivize a hyperbolic developing map by composing `dev` with
`ℍ ⊂ ℂP¹` and complexifying its real holonomy.

%%handwave
name:
  Projectivized package associated to a hyperbolic developing map
statement:
  Given a hyperbolic developing map whose projectivization is equivariant, package $\iota\circ\mathrm{dev}$ with the complexified real holonomy and its projective regularity.
-/
def toProjectivized (D : HyperbolicDevelopingMap X x₀ g)
    (h_equivariant : D.ProjectiveEquivariant D.projectiveHolonomy) :
    ProjectivizedHyperbolicDevelopingMap X x₀ g where
  hyperbolicDevelopingMap := D
  projectiveHolonomy := D.projectiveHolonomy
  projectiveHolonomy_complexifies_real := D.projectiveHolonomy_complexifies_real
  projective_regular := D.projectivizedDevelopingMapRegularity
  projective_equivariant := h_equivariant

end HyperbolicDevelopingMap

namespace LiftedHyperbolicDevelopingMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

end LiftedHyperbolicDevelopingMap

namespace HyperbolicDevelopingPipeline

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

end HyperbolicDevelopingPipeline

namespace HyperbolicDevelopingConstructionPipeline

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

end HyperbolicDevelopingConstructionPipeline

namespace HyperbolicDevelopingCurvaturePipeline

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

end HyperbolicDevelopingCurvaturePipeline

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

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

%%handwave
name:
  Local-homeomorphism data for a descended developing branch
statement:
  A descended projective branch that agrees with a projective chart, is continuous, and has a holomorphic finite coordinate with nonzero derivative determines the full local-homeomorphism certificate for that branch.
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

%%handwave
name:
  Complex compatibility of a finite developing coordinate
statement:
  A finite holomorphic coordinate for a descended developing branch, with nonzero derivative, supplies compatibility between its projective chart and the complex chart used to parametrize the branch.
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

/-- The source of a branch chart is open.
%%handwave
name:
  Openness of the source of a descended projective chart
statement:
  For every local projective chart $C$ descended from a projectivized developing map, the source of $C$ is open in $X$.
proof:
  The source of any local homeomorphism is open.
-/
theorem source_open
    (C : ProjectiveLocalChartFromDevelopingMap X D) :
    IsOpen C.chart.source :=
  C.branch_local_homeomorphism.source_open

/-- The source of a developing branch is covered by its selected complex chart.
%%handwave
name:
  The branch source lies in its selected complex-coordinate chart
statement:
  For every descended projective chart $C$, the source of $C$ is contained in the source of the complex chart selected for its local biholomorphic branch.
proof:
  This is the stored inclusion of the branch source in the source complex-coordinate chart.
-/
theorem source_subset_sourceComplexChart_source
    (C : ProjectiveLocalChartFromDevelopingMap X D) :
    C.chart.source ⊆ C.branch_local_homeomorphism.sourceComplexChart.source :=
  C.branch_local_homeomorphism.chart_source_subset_sourceComplexChart_source

/-- A developing branch is compatible with its selected source complex chart.
%%handwave
name:
  Compatibility of a developing branch with its source coordinate
statement:
  Every descended projective developing branch carries the projective-to-complex chart compatibility determined by its selected finite source coordinate.
-/
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



namespace ProjectiveDevelopingAtlasRiemannSurfaceCompatibilityData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}
    {D : ProjectivizedHyperbolicDevelopingMap X x₀ g}

/--
Any atlas of constructed developing branch charts has Riemann-surface
compatibility in the selected source complex charts.

%%handwave
name:
  Riemann-surface compatibility of selected developing charts
statement:
  A choice of descended projective developing chart at each point determines compatibility data with the original Riemann-surface atlas through the finite complex coordinate selected for each branch.
-/
def ofChartAt
    (chartAt : X → ProjectiveLocalChartFromDevelopingMap X D) :
    ProjectiveDevelopingAtlasRiemannSurfaceCompatibilityData X chartAt where
  projective_source_open := fun x ↦ (chartAt x).source_open
  complex_source_open := fun e _he ↦ e.open_source
  projective_complex_compatible := fun x ↦
    (chartAt x).sourceComplexChartCompatibility

end ProjectiveDevelopingAtlasRiemannSurfaceCompatibilityData

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

/-- The local projective chart from the developing map near `x`.
%%handwave
name:
  Selected projective developing chart at a point
statement:
  For a projective atlas descended from a developing map, the local chart at $x\in X$ is the projective chart selected by its developing-branch atlas at $x$.
-/
def localChartAt (A : ProjectiveAtlasFromDevelopingMap X D) (x : X) :
    ProjectiveChart X :=
  (A.developingAtlas.chartAt x).chart

/--
%%handwave
name:
  Selected developing charts belong to the projective atlas
statement:
  For every developing atlas $A$ and point $x\in X$, the selected local developing chart at $x$ belongs to the atlas of the induced projective structure.
proof:
  This is the assertion that the chosen local developing chart is a local inverse branch, stored for every $x$ in the atlas package.
-/
theorem localChartAt_mem_atlas
    (A : ProjectiveAtlasFromDevelopingMap X D) (x : X) :
    A.localChartAt x ∈ A.projectiveStructure.atlasSet :=
  A.charts_are_local_inverse_branches x

/--
The holonomy attached to the constructed projective atlas is the complexified
real holonomy of the original hyperbolic developing map.
%%handwave
name:
  The holonomy attached to the constructed projective atlas is the complexified real holonomy of the original hyperbolic developing map
statement:
  The holonomy attached to the constructed projective atlas is the complexified
  real holonomy of the original hyperbolic developing map.
proof:
  Use the stored equality identifying the projective holonomy with the complexification of the hyperbolic real holonomy.
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

end ProjectiveAtlasFromDevelopingMap




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

/-- An inducing hyperbolic developing map gives an existential `PSL(2, ℝ)` holonomy certificate.
%%handwave
name:
  An inducing hyperbolic metric yields real projective holonomy
statement:
  If a complex projective structure $P$ is induced by a hyperbolic metric $g$, then there is a basepoint $x_0$ such that the holonomy of $P$ is certified, through its developing atlas, to lie in $\mathrm{PSL}_2(\mathbb R)$.
proof:
  Choose the basepoint, projectivized developing map, and atlas witnessing induction by $g$; then apply [the holonomy of the resulting developing atlas is the complexification of real holonomy](lean:JJMath.ProjectiveAtlasFromDevelopingMap.hasPSL2RHolonomy).
-/
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

end HyperbolicMetric

end

end JJMath
