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

/--
A lift of real holonomy to `SL(2, ℝ)`.  This is often the most convenient
formal package because mathlib already has the `SL(2, ℝ)` action on `ℍ`.
-/
structure RealHolonomyLift (X : Type*) [TopologicalSpace X] (x₀ : X) where
  /-- Lifted holonomy in `SL(2, ℝ)`. -/
  toMonoidHom : FundamentalGroup X x₀ →* RealMobiusRepresentative

namespace RealHolonomyLift

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

noncomputable instance : CoeFun (RealHolonomyLift X x₀)
    (fun _ ↦ FundamentalGroup X x₀ → RealMobiusRepresentative) where
  coe ρ := ρ.toMonoidHom

/-- The action on `ℍ` induced by lifted holonomy. -/
def upperHalfPlaneAction (ρ : RealHolonomyLift X x₀)
    (γ : FundamentalGroup X x₀) (z : ℍ) : ℍ :=
  realMobiusRepresentativeAction (ρ γ) z

/--
%%handwave
name:
  The lifted real holonomy fixes points under the identity loop
statement:
  For every lifted holonomy representation $\widetilde\rho:\pi_1(X,x_0)\to
  \mathrm{SL}_2(\mathbb R)$ and every $z\in\mathbb H$, one has
  $\widetilde\rho(1)\cdot z=z$.
proof:
  The homomorphism sends the identity loop to the identity matrix, whose Möbius action fixes $z$.
-/
@[simp]
theorem upperHalfPlaneAction_one (ρ : RealHolonomyLift X x₀) (z : ℍ) :
    ρ.upperHalfPlaneAction 1 z = z := by
  simp [upperHalfPlaneAction]

/--
%%handwave
name:
  The lifted real holonomy action respects multiplication
statement:
  For every lifted holonomy representation $\widetilde\rho$, loops
  $\gamma,\delta\in\pi_1(X,x_0)$, and $z\in\mathbb H$, one has
  $\widetilde\rho(\gamma\delta)\cdot z=
  \widetilde\rho(\gamma)\cdot(\widetilde\rho(\delta)\cdot z)$.
proof:
  Use multiplicativity of $\widetilde\rho$ and associativity of the $\mathrm{SL}_2(\mathbb R)$ action on $\mathbb H$.
-/
@[simp]
theorem upperHalfPlaneAction_mul (ρ : RealHolonomyLift X x₀)
    (γ δ : FundamentalGroup X x₀) (z : ℍ) :
    ρ.upperHalfPlaneAction (γ * δ) z =
      ρ.upperHalfPlaneAction γ (ρ.upperHalfPlaneAction δ z) := by
  simp [upperHalfPlaneAction]

/-- Project a lifted `SL(2, ℝ)` holonomy representation to `PSL(2, ℝ)`. -/
def toRealHolonomyRepresentation (ρ : RealHolonomyLift X x₀) :
    RealHolonomyRepresentation X x₀ where
  toMonoidHom := realMobiusProjection.comp ρ.toMonoidHom

end RealHolonomyLift

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

/--
%%handwave
name:
  Multiplicativity of real projective holonomy
statement:
  If $\rho:\pi_1(X,x_0)\to\mathrm{PSL}_2(\mathbb R)$ is a real holonomy
  representation and $\gamma,\delta\in\pi_1(X,x_0)$, then
  $\rho(\gamma\delta)=\rho(\gamma)\rho(\delta)$.
proof:
  This is the multiplication law for the homomorphism $\rho$.
-/
@[simp]
theorem map_mul (ρ : RealHolonomyRepresentation X x₀) (γ δ : FundamentalGroup X x₀) :
    ρ (γ * δ) = ρ γ * ρ δ :=
  ρ.toMonoidHom.map_mul γ δ

/-- The canonical upper-half-plane action induced by real projective holonomy. -/
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

/--
%%handwave
name:
  The real projective holonomy action respects multiplication
statement:
  For every real projective holonomy representation $\rho$, loops
  $\gamma,\delta\in\pi_1(X,x_0)$, and $z\in\mathbb H$, one has
  $\rho(\gamma\delta)\cdot z=\rho(\gamma)\cdot(\rho(\delta)\cdot z)$.
proof:
  Combine multiplicativity of $\rho$ with the group-action law on $\mathbb H$.
-/
@[simp]
theorem upperHalfPlaneAction_mul (ρ : RealHolonomyRepresentation X x₀)
    (γ δ : FundamentalGroup X x₀) (z : ℍ) :
    ρ.upperHalfPlaneAction (γ * δ) z =
      ρ.upperHalfPlaneAction γ (ρ.upperHalfPlaneAction δ z) := by
  simp [upperHalfPlaneAction]

/--
The unlifted real holonomy action is induced by a concrete `SL(2, ℝ)` lift.

This ties the stored `PSL(2, ℝ)` homomorphism and the stored action on `ℍ` to
the same lifted Mobius representatives.
-/
def IsInducedByLift (ρ : RealHolonomyRepresentation X x₀)
    (ρLift : RealHolonomyLift X x₀) : Prop :=
  ρ.toMonoidHom = realMobiusProjection.comp ρLift.toMonoidHom ∧
    ∀ γ z, ρ.upperHalfPlaneAction γ z = ρLift.upperHalfPlaneAction γ z

end RealHolonomyRepresentation

namespace RealHolonomyLift

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

/-- The real holonomy representation obtained from a lift is induced by that lift.
%%handwave
name:
  Projection of lifted real holonomy
statement:
  For every lifted holonomy $\widetilde\rho:\pi_1(X,x_0)\to\mathrm{SL}_2(\mathbb R)$, its projection $\rho$ to $\mathrm{PSL}_2(\mathbb R)$ satisfies $\rho=\pi\circ\widetilde\rho$ and $\rho(\gamma)\cdot z=\widetilde\rho(\gamma)\cdot z$ for every loop $\gamma$ and $z\in\mathbb H$.
proof:
  The projected homomorphism agrees by definition. For each loop, the action of its $\mathrm{PSL}_2(\mathbb R)$ class is the action of the chosen $\mathrm{SL}_2(\mathbb R)$ representative.
-/
theorem toRealHolonomyRepresentation_isInducedByLift (ρ : RealHolonomyLift X x₀) :
    ρ.toRealHolonomyRepresentation.IsInducedByLift ρ := by
  constructor
  · rfl
  · intro γ z
    change realMobiusAction (realMobiusProjection (ρ.toMonoidHom γ)) z =
      realMobiusRepresentativeAction (ρ.toMonoidHom γ) z
    simp

end RealHolonomyLift

/--
Chartwise holomorphicity for a global upper-half-plane developing map.

At each point of the cover we express the map in the complex source chart and
then view its upper-half-plane value as a complex number.
-/
def HyperbolicDevelopingMapHolomorphic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x₀ : X} (cover : SimplyConnectedCover X x₀)
    (dev : cover.total → ℍ) : Prop :=
  ∀ y : cover.total,
    DifferentiableAt ℂ
      (fun z : ℂ ↦ ((dev ((chartAt ℂ y).symm z) : ℍ) : ℂ))
      ((chartAt ℂ y) y)

/-- The local complex-coordinate expression of an upper-half-plane developing map. -/
def HyperbolicDevelopingMapCoordinateExpression
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x₀ : X} (cover : SimplyConnectedCover X x₀)
    (dev : cover.total → ℍ) (y : cover.total) : ℂ → ℂ :=
  fun z : ℂ ↦ ((dev ((chartAt ℂ y).symm z) : ℍ) : ℂ)

/--
Nonvanishing local derivative for the upper-half-plane developing map in
complex coordinates.  This is the local-biholomorphism boundary needed by the
projectivization/projective-atlas construction.
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

/-- A regular developing map carries concrete local-biholomorphism branch data.
%%handwave
name:
  Local biholomorphic branches from developing-map regularity
statement:
  Let $d:\widetilde X\to\mathbb H$ be a regular developing map. At every $y\in\widetilde X$ there is a local complex homeomorphism branch agreeing with the coordinate expression of $d$, holomorphic on its source, and having nonzero derivative there.
proof:
  Take the stored local-homeomorphism branch data from the regularity package.
-/
theorem local_biholomorphism_data_holds (h : HyperbolicDevelopingMapRegularity cover dev) :
    HyperbolicDevelopingMapLocalBiholomorphismData cover dev :=
  h.local_biholomorphism_data

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

/--
A developing map whose real holonomy has been lifted to `SL(2, ℝ)`.

This is a technically convenient variant of `HyperbolicDevelopingMap`: the
equivariance equation uses the concrete `SL(2, ℝ)` action on `ℍ` already present
in mathlib.
-/
structure LiftedHyperbolicDevelopingMap (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
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
  /-- Lifted holonomy in `SL(2, ℝ)`. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Pullback identity: `dev^* g_ℍ = projection^* g`. -/
  pullback_metric :
    PullsBackMetric dev upperHalfPlaneConformalMetric coverMetric
  /-- Equivariance with respect to deck transformations and lifted holonomy. -/
  equivariant :
    ∀ γ y, dev (cover.deckAction γ y) = holonomyLift.upperHalfPlaneAction γ (dev y)

namespace HyperbolicDevelopingMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- The regularity field implies continuity of the developing map.
%%handwave
name:
  Continuity of a hyperbolic developing map
statement:
  For every hyperbolic developing map $D:\widetilde X_{x_0}\to\mathbb H$, the map $D$ is continuous.
proof:
  This is the continuity field stored in the regularity package of $D$.
-/
theorem dev_continuous (D : HyperbolicDevelopingMap X x₀ g) :
    Continuous D.dev :=
  D.dev_regular.continuous

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

/-- The regularity field implies continuity of the lifted developing map.
%%handwave
name:
  Continuity of a lifted hyperbolic developing map
statement:
  For every hyperbolic developing map $D:\widetilde X_{x_0}\to\mathbb H$ with lifted $\mathrm{SL}_2(\mathbb R)$ holonomy, the map $D$ is continuous.
proof:
  This is the continuity field stored in the regularity package of the lifted map $D$.
-/
theorem dev_continuous (D : LiftedHyperbolicDevelopingMap X x₀ g) :
    Continuous D.dev :=
  D.dev_regular.continuous

/-- The regularity field implies chartwise holomorphicity of the lifted developing map.
%%handwave
name:
  Chartwise holomorphicity of a lifted hyperbolic developing map
statement:
  For every lifted hyperbolic developing map $D$ and $y\in\widetilde X_{x_0}$, the coordinate expression $z\mapsto D(\varphi_y^{-1}(z))$ is complex differentiable at $\varphi_y(y)$.
proof:
  Apply [a regular developing map is holomorphic in local complex coordinates](lean:JJMath.HyperbolicDevelopingMapRegularity.holomorphic) to the regularity package of the lifted map $D$.
-/
theorem dev_holomorphic (D : LiftedHyperbolicDevelopingMap X x₀ g) :
    HyperbolicDevelopingMapHolomorphic D.cover D.dev :=
  D.dev_regular.holomorphic

/-- The regularity field implies local-biholomorphicity of the lifted developing map.
%%handwave
name:
  Nonvanishing derivative of a lifted hyperbolic developing map
statement:
  For every lifted hyperbolic developing map $D$ and $y\in\widetilde X_{x_0}$, the derivative of the coordinate expression of $D$ at $\varphi_y(y)$ is nonzero.
proof:
  Apply [a regular developing map has nonzero coordinate derivative everywhere](lean:JJMath.HyperbolicDevelopingMapRegularity.locally_biholomorphic) to the regularity package of the lifted map $D$.
-/
theorem dev_locally_biholomorphic (D : LiftedHyperbolicDevelopingMap X x₀ g) :
    HyperbolicDevelopingMapLocallyBiholomorphic D.cover D.dev :=
  D.dev_regular.locally_biholomorphic

/-- The regularity field gives local-biholomorphism branch data for the lifted developing map.
%%handwave
name:
  Local biholomorphic branches of a lifted developing map
statement:
  For every lifted hyperbolic developing map $D$ and $y\in\widetilde X_{x_0}$, there is a local complex homeomorphism branch agreeing with the coordinate expression of $D$, holomorphic with nonzero derivative on its source.
proof:
  This is the local-biholomorphism branch-data field stored in the regularity package of the lifted map $D$.
-/
theorem dev_local_biholomorphism_data (D : LiftedHyperbolicDevelopingMap X x₀ g) :
    HyperbolicDevelopingMapLocalBiholomorphismData D.cover D.dev :=
  D.dev_regular.local_biholomorphism_data

/-- Forget a lifted developing map to a `PSL(2, ℝ)`-valued developing map. -/
def toHyperbolicDevelopingMap (D : LiftedHyperbolicDevelopingMap X x₀ g) :
    HyperbolicDevelopingMap X x₀ g where
  cover := D.cover
  dev := D.dev
  coverMetric := D.coverMetric
  coverMetric_pullback := D.coverMetric_pullback
  dev_regular := D.dev_regular
  holonomy := D.holonomyLift.toRealHolonomyRepresentation
  pullback_metric := D.pullback_metric
  equivariant := by
    intro γ y
    trans D.holonomyLift.upperHalfPlaneAction γ (D.dev y)
    · exact D.equivariant γ y
    · symm
      exact (D.holonomyLift.toRealHolonomyRepresentation_isInducedByLift).2 γ (D.dev y)

end LiftedHyperbolicDevelopingMap

/--
Developing-map theorem target: every smooth conformal metric of curvature `-1`
has a developing map to the upper half-plane on the universal cover.
-/
def HyperbolicMetric.AdmitsDevelopingMap {X : Type} [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] (x₀ : X)
    (g : HyperbolicMetric X) : Prop :=
  Nonempty (HyperbolicDevelopingMap X x₀ g)

/--
Variant of the developing-map theorem target where the holonomy is lifted to
`SL(2, ℝ)`.
-/
def HyperbolicMetric.AdmitsLiftedDevelopingMap {X : Type} [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] (x₀ : X)
    (g : HyperbolicMetric X) : Prop :=
  Nonempty (LiftedHyperbolicDevelopingMap X x₀ g)

/--
%%handwave
name:
  The metric admits developing map from admits lifted developing map
statement:
  Let $g$ be a hyperbolic metric on a Riemann surface $X$ and $x_0\in X$.
  If $g$ has a developing map on a simply connected cover with holonomy lifted
  to $\mathrm{SL}_2(\mathbb R)$, then it has a developing map with
  $\mathrm{PSL}_2(\mathbb R)$ holonomy.
proof:
  Choose the lifted developing map and project its lifted holonomy to $\mathrm{PSL}_2(\mathbb R)$; all other developing-map data are unchanged.
-/
theorem HyperbolicMetric.admitsDevelopingMap_of_admitsLiftedDevelopingMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsLiftedDevelopingMap x₀) :
    g.AdmitsDevelopingMap x₀ :=
  h.elim fun D ↦ ⟨D.toHyperbolicDevelopingMap⟩

end

end JJMath
