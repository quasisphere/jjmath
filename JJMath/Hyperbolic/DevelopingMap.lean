import JJMath.Hyperbolic.UpperHalfPlane
import JJMath.Hyperbolic.Cover
import JJMath.ProjectiveGeometry.RealMobius

/-!
# Hyperbolic developing maps

The developing map of a hyperbolic metric is single-valued on the universal
cover and equivariant with respect to a `PSL(2, ℝ)` holonomy representation.
-/

namespace JJMath

open UpperHalfPlane
open scoped MatrixGroups

noncomputable section

/-- Holonomy of a hyperbolic metric, valued in `PSL(2, ℝ)`. -/
structure RealHolonomyRepresentation (X : Type*) [TopologicalSpace X] (x₀ : X) where
  /-- The holonomy homomorphism. -/
  toMonoidHom : FundamentalGroup X x₀ →* RealMobiusGroup



namespace RealHolonomyRepresentation

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

noncomputable instance : CoeFun (RealHolonomyRepresentation X x₀)
    (fun _ ↦ FundamentalGroup X x₀ → RealMobiusGroup) where
  coe ρ := ρ.toMonoidHom

/--
%%handwave
name:
  Real projective holonomy sends the identity loop to the identity
statement:
  If $\rho:\pi_1(X,x_0)\to\mathrm{PSL}_2(\mathbb R)$ is a real holonomy
  representation, then $\rho(1)=1$.
proof:
  This is the identity law for the homomorphism $\rho$.
-/
@[simp]
theorem map_one (ρ : RealHolonomyRepresentation X x₀) :
    ρ (1 : FundamentalGroup X x₀) = 1 :=
  ρ.toMonoidHom.map_one

/-- The canonical upper-half-plane action induced by real projective holonomy.
%%handwave
name:
  Upper-half-plane action of real holonomy
statement:
  A real holonomy representation $\rho:\pi_1(X,x_0)\to\mathrm{PSL}_2(\mathbb R)$ acts on $\mathbb H$ by $(\gamma,z)\mapsto \rho(\gamma)\cdot z$ through the standard Möbius action.
-/
def upperHalfPlaneAction (ρ : RealHolonomyRepresentation X x₀)
    (γ : FundamentalGroup X x₀) (z : ℍ) : ℍ :=
  realMobiusAction (ρ γ) z

/--
%%handwave
name:
  Real projective holonomy fixes points under the identity loop
statement:
  For every real projective holonomy representation $\rho$ and every
  $z\in\mathbb H$, one has $\rho(1)\cdot z=z$.
proof:
  The identity law gives $\rho(1)=1$, and the identity element of $\mathrm{PSL}_2(\mathbb R)$ acts trivially on $\mathbb H$.
-/
@[simp]
theorem upperHalfPlaneAction_one (ρ : RealHolonomyRepresentation X x₀) (z : ℍ) :
    ρ.upperHalfPlaneAction 1 z = z := by
  simp [upperHalfPlaneAction]

end RealHolonomyRepresentation


/--
Chartwise holomorphicity for a global upper-half-plane developing map.

At each point of the cover we express the map in the complex source chart and
then view its upper-half-plane value as a complex number.

%%handwave
name:
  Chartwise holomorphic upper-half-plane developing map
statement:
  A map $\mathrm{dev}:\widetilde X\to\mathbb H$ is chartwise holomorphic when its complex-valued expression in a source chart is complex differentiable at the coordinate of every point of $\widetilde X$.
-/
def HyperbolicDevelopingMapHolomorphic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x₀ : X} (cover : SimplyConnectedCover X x₀)
    (dev : cover.total → ℍ) : Prop :=
  ∀ y : cover.total,
    DifferentiableAt ℂ
      (fun z : ℂ ↦ ((dev ((chartAt ℂ y).symm z) : ℍ) : ℂ))
      ((chartAt ℂ y) y)

/-- The local complex-coordinate expression of an upper-half-plane developing map.
%%handwave
name:
  Complex coordinate expression of a developing map
statement:
  At $y\in\widetilde X$, the coordinate expression of $\mathrm{dev}:\widetilde X\to\mathbb H$ is $z\mapsto \mathrm{dev}(\varphi_y^{-1}(z))$, regarded as a complex-valued function.
-/
def HyperbolicDevelopingMapCoordinateExpression
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x₀ : X} (cover : SimplyConnectedCover X x₀)
    (dev : cover.total → ℍ) (y : cover.total) : ℂ → ℂ :=
  fun z : ℂ ↦ ((dev ((chartAt ℂ y).symm z) : ℍ) : ℂ)

/--
Nonvanishing local derivative for the upper-half-plane developing map in
complex coordinates.  This is the local-biholomorphism boundary needed by the
projectivization/projective-atlas construction.

%%handwave
name:
  Locally biholomorphic hyperbolic developing map
statement:
  An upper-half-plane developing map is locally biholomorphic when the derivative of its complex coordinate expression is nonzero at every point of the covering surface.
-/
def HyperbolicDevelopingMapLocallyBiholomorphic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x₀ : X} (cover : SimplyConnectedCover X x₀)
    (dev : cover.total → ℍ) : Prop :=
  ∀ y : cover.total,
    deriv (HyperbolicDevelopingMapCoordinateExpression cover dev y) ((chartAt ℂ y) y) ≠ 0

/--
Concrete local-homeomorphism branch data for an upper-half-plane developing
map in finite complex coordinates.

%%handwave
name:
  Local biholomorphism branches of a developing map
statement:
  This property assigns at every point $y\in\widetilde X$ a complex local homeomorphism agreeing with the coordinate expression of $\mathrm{dev}$ near $y$, holomorphic there, and having nonzero derivative throughout its domain.
-/
def HyperbolicDevelopingMapLocalBiholomorphismData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x₀ : X} (cover : SimplyConnectedCover X x₀)
    (dev : cover.total → ℍ) : Prop :=
  ∀ y : cover.total, ∃ branch : OpenPartialHomeomorph ℂ ℂ,
    ((chartAt ℂ y) y) ∈ branch.source ∧
      branch.source ⊆ (chartAt ℂ y).target ∧
      ∀ z ∈ branch.source,
        branch z = HyperbolicDevelopingMapCoordinateExpression cover dev y z ∧
          DifferentiableAt ℂ branch z ∧ deriv branch z ≠ 0

/--
Concrete regularity boundary for a global upper-half-plane developing map.

This is now strong enough to imply the chartwise holomorphicity predicate used
by downstream Schwarzian and projective-structure constructions.
-/
structure HyperbolicDevelopingMapRegularity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x₀ : X} (cover : SimplyConnectedCover X x₀)
    (dev : cover.total → ℍ) : Prop where
  /-- The developing map is continuous as a map into `ℍ`. -/
  continuous : Continuous dev
  /-- The developing map is holomorphic in local complex coordinates. -/
  chartwise_holomorphic : HyperbolicDevelopingMapHolomorphic cover dev
  /-- The local complex-coordinate expression has nonzero derivative. -/
  local_biholomorphic : HyperbolicDevelopingMapLocallyBiholomorphic cover dev
  /-- The local complex-coordinate expression is represented by local homeomorphism branches. -/
  local_biholomorphism_data : HyperbolicDevelopingMapLocalBiholomorphismData cover dev

namespace HyperbolicDevelopingMapRegularity

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x₀ : X} {cover : SimplyConnectedCover X x₀} {dev : cover.total → ℍ}

/-- A regular developing map is holomorphic in local complex coordinates.
%%handwave
name:
  Chartwise holomorphicity from developing-map regularity
statement:
  Let $p:\widetilde X\to X$ be a simply connected cover and $d:\widetilde X\to\mathbb H$ a regular developing map. For every $y\in\widetilde X$, the coordinate expression $z\mapsto d(\varphi_y^{-1}(z))$ is complex differentiable at $\varphi_y(y)$.
proof:
  Take the stored chartwise-holomorphicity field of the regularity package.
-/
theorem holomorphic (h : HyperbolicDevelopingMapRegularity cover dev) :
    HyperbolicDevelopingMapHolomorphic cover dev :=
  h.chartwise_holomorphic

/-- A regular developing map is locally biholomorphic in complex coordinates.
%%handwave
name:
  Nonvanishing coordinate derivative from developing-map regularity
statement:
  Let $d:\widetilde X\to\mathbb H$ be a regular developing map. For every $y\in\widetilde X$, the derivative of $z\mapsto d(\varphi_y^{-1}(z))$ at $\varphi_y(y)$ is nonzero.
proof:
  Take the stored nonvanishing-derivative field of the regularity package.
-/
theorem locally_biholomorphic (h : HyperbolicDevelopingMapRegularity cover dev) :
    HyperbolicDevelopingMapLocallyBiholomorphic cover dev :=
  h.local_biholomorphic

end HyperbolicDevelopingMapRegularity

/--
%%handwave
name:
  Hyperbolic developing map
statement:
  A developing map for a hyperbolic metric $g$ on a Riemann surface
  $X$ consists of a holomorphic local biholomorphism
  $\operatorname{dev}:\widetilde X_{x_0}\to\mathbb H$ on a simply connected
  cover, together with a representation
  $\rho:\pi_1(X,x_0)\to\mathrm{PSL}_2(\mathbb R)$. It satisfies
  $\operatorname{dev}(\gamma\cdot y)=\rho(\gamma)\operatorname{dev}(y)$ and
  $\operatorname{dev}^{*}g_{\mathbb H}=\pi^{*}g$.
-/
structure HyperbolicDevelopingMap (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) (g : HyperbolicMetric X) where
  /-- The simply connected cover on which the developing map is single-valued. -/
  cover : SimplyConnectedCover X x₀
  /-- The developing map into the upper half-plane. -/
  dev : cover.total → ℍ
  /-- The pullback of `g` to the cover. -/
  coverMetric : ConformalMetric cover.total
  /-- The cover metric is the pullback of the base metric along the projection. -/
  coverMetric_pullback :
    PullsBackMetric cover.projection g.toConformalMetric coverMetric
  /-- The developing map has the concrete holomorphic local-biholomorphic regularity on the cover. -/
  dev_regular : HyperbolicDevelopingMapRegularity cover dev
  /-- The `PSL(2, ℝ)` holonomy representation. -/
  holonomy : RealHolonomyRepresentation X x₀
  /-- Pullback identity: `dev^* g_ℍ = projection^* g`. -/
  pullback_metric :
    PullsBackMetric dev upperHalfPlaneConformalMetric coverMetric
  /-- Equivariance with respect to deck transformations and holonomy. -/
  equivariant :
    ∀ γ y, dev (cover.deckAction γ y) = holonomy.upperHalfPlaneAction γ (dev y)

namespace HyperbolicDevelopingMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- The regularity field implies chartwise holomorphicity of the developing map.
%%handwave
name:
  Chartwise holomorphicity of a hyperbolic developing map
statement:
  For every hyperbolic developing map $D$ and $y\in\widetilde X_{x_0}$, the coordinate expression $z\mapsto D(\varphi_y^{-1}(z))$ is complex differentiable at $\varphi_y(y)$.
proof:
  Apply [a regular developing map is holomorphic in local complex coordinates](lean:JJMath.HyperbolicDevelopingMapRegularity.holomorphic) to the regularity package of $D$.
-/
theorem dev_holomorphic (D : HyperbolicDevelopingMap X x₀ g) :
    HyperbolicDevelopingMapHolomorphic D.cover D.dev :=
  D.dev_regular.holomorphic

/-- The regularity field implies local-biholomorphicity of the developing map.
%%handwave
name:
  Nonvanishing derivative of a hyperbolic developing map
statement:
  For every hyperbolic developing map $D$ and $y\in\widetilde X_{x_0}$, the derivative of the coordinate expression of $D$ at $\varphi_y(y)$ is nonzero.
proof:
  Apply [a regular developing map has nonzero coordinate derivative everywhere](lean:JJMath.HyperbolicDevelopingMapRegularity.locally_biholomorphic) to the regularity package of $D$.
-/
theorem dev_locally_biholomorphic (D : HyperbolicDevelopingMap X x₀ g) :
    HyperbolicDevelopingMapLocallyBiholomorphic D.cover D.dev :=
  D.dev_regular.locally_biholomorphic

/-- The regularity field gives local-biholomorphism branch data for the developing map.
%%handwave
name:
  Local biholomorphic branches of a hyperbolic developing map
statement:
  For every hyperbolic developing map $D$ and $y\in\widetilde X_{x_0}$, there is a local complex homeomorphism branch agreeing with the coordinate expression of $D$, holomorphic with nonzero derivative on its source.
proof:
  This is the local-biholomorphism branch-data field stored in the regularity package of $D$.
-/
theorem dev_local_biholomorphism_data (D : HyperbolicDevelopingMap X x₀ g) :
    HyperbolicDevelopingMapLocalBiholomorphismData D.cover D.dev :=
  D.dev_regular.local_biholomorphism_data

end HyperbolicDevelopingMap

namespace LiftedHyperbolicDevelopingMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

end LiftedHyperbolicDevelopingMap

end

end JJMath
