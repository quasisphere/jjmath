import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Topology.Connected.Clopen
import JJMath.Hyperbolic.Schwarzian.Frobenius

/-!
# Split Schwarzian developing-map constructions
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

structure LocalSchwarzianODEChart {u : LocalConformalFactor}
    (S : LocalSchwarzianData u) where
  /-- The smaller coordinate domain on which the ODE solution frame is defined. -/
  domain : Set ℂ
  /-- The chart domain is open. -/
  isOpen_domain : IsOpen domain
  /-- The local domain lies inside the coefficient domain. -/
  domain_subset : domain ⊆ u.coordinateDomain
  /-- The solution-frame data for `{f,z} = S.coefficient z`. -/
  frame : SchwarzianLinearODEFrame S.coefficient domain

namespace LocalSchwarzianODEChart

/-- The local projective/developing coordinate obtained by solving the Schwarzian ODE. -/
def localMap {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (C : LocalSchwarzianODEChart S) : ℂ → ℂ :=
  C.frame.localMap

/-- The constructed local coordinate has Schwarzian coefficient `S.coefficient`. -/
theorem schwarzian_eq_coefficient
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (C : LocalSchwarzianODEChart S) :
    ∀ z, z ∈ C.domain →
      schwarzianExpression C.frame.localMapDeriv C.frame.localMapSecondDeriv
        C.frame.localMapThirdDeriv z = S.coefficient z :=
  C.frame.schwarzianExpression_eq_coefficient

/-- The constructed local coordinate has nonzero first derivative. -/
theorem localMapDeriv_ne_zero
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (C : LocalSchwarzianODEChart S) :
    ∀ z, z ∈ C.domain → C.frame.localMapDeriv z ≠ 0 :=
  C.frame.localMapDeriv_ne_zero

end LocalSchwarzianODEChart

/--
A local projective developing map produced by the Schwarzian equation.

The affine coordinate is the ratio `y₁ / y₀`; the projective coordinate is the
same map viewed in the finite affine chart of the Riemann sphere.  The package
keeps the Schwarzian equation and nonzero-derivative witness from the ODE frame.
-/
structure LocalProjectiveDevelopingMap {u : LocalConformalFactor}
    (S : LocalSchwarzianData u) where
  /-- The local coordinate domain. -/
  domain : Set ℂ
  /-- The local coordinate domain is open. -/
  isOpen_domain : IsOpen domain
  /-- The local coordinate domain lies in the coefficient domain. -/
  domain_subset : domain ⊆ u.coordinateDomain
  /-- The affine developing coordinate. -/
  affineMap : ℂ → ℂ
  /-- The same coordinate viewed as a Riemann-sphere-valued projective map. -/
  projectiveMap : ℂ → RiemannSphere
  /-- The projective map is the finite affine inclusion of `affineMap`. -/
  projectiveMap_eq_affine : ∀ z, z ∈ domain → projectiveMap z = (affineMap z : RiemannSphere)
  /-- The projective developing map avoids infinity on this affine chart. -/
  projectiveMap_ne_infty : ∀ z, z ∈ domain → projectiveMap z ≠ (OnePoint.infty : RiemannSphere)
  /-- Symbolic first derivative of the affine developing coordinate. -/
  affineMapDeriv : ℂ → ℂ
  /-- Symbolic second derivative of the affine developing coordinate. -/
  affineMapSecondDeriv : ℂ → ℂ
  /-- Symbolic third derivative of the affine developing coordinate. -/
  affineMapThirdDeriv : ℂ → ℂ
  /-- The affine coordinate has nonzero first derivative on the domain. -/
  affineMapDeriv_ne_zero : ∀ z, z ∈ domain → affineMapDeriv z ≠ 0
  /-- The affine coordinate has Schwarzian coefficient `S.coefficient`. -/
  schwarzian_eq_coefficient : ∀ z, z ∈ domain →
    schwarzianExpression affineMapDeriv affineMapSecondDeriv affineMapThirdDeriv z =
      S.coefficient z

namespace LocalProjectiveDevelopingMap

/-- The affine developing coordinate of a local projective developing map. -/
def localMap {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) : ℂ → ℂ :=
  D.affineMap

/-- Restrict a local projective developing map to an open subdomain. -/
def restrict {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) (V : Set ℂ)
    (hVOpen : IsOpen V) (hVsub : V ⊆ D.domain) :
    LocalProjectiveDevelopingMap S where
  domain := V
  isOpen_domain := hVOpen
  domain_subset := fun _ hz ↦ D.domain_subset (hVsub hz)
  affineMap := D.affineMap
  projectiveMap := D.projectiveMap
  projectiveMap_eq_affine := fun z hz ↦
    D.projectiveMap_eq_affine z (hVsub hz)
  projectiveMap_ne_infty := fun z hz ↦
    D.projectiveMap_ne_infty z (hVsub hz)
  affineMapDeriv := D.affineMapDeriv
  affineMapSecondDeriv := D.affineMapSecondDeriv
  affineMapThirdDeriv := D.affineMapThirdDeriv
  affineMapDeriv_ne_zero := fun z hz ↦
    D.affineMapDeriv_ne_zero z (hVsub hz)
  schwarzian_eq_coefficient := fun z hz ↦
    D.schwarzian_eq_coefficient z (hVsub hz)

@[simp]
theorem restrict_domain {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) (V : Set ℂ)
    (hVOpen : IsOpen V) (hVsub : V ⊆ D.domain) :
    (D.restrict V hVOpen hVsub).domain = V :=
  rfl

end LocalProjectiveDevelopingMap

/--
Concrete holomorphicity predicate for an upper-half-plane-valued local branch.

We phrase this pointwise as complex differentiability of the complex-valued
coercion on the relevant open domain.  This is the shape most of the local
Schwarzian and pullback API already consumes.
-/
def LocalUpperHalfPlaneMapHolomorphicOn (U : Set ℂ) (f : ℂ → ℍ) : Prop :=
  ∀ z, z ∈ U → DifferentiableAt ℂ (fun w : ℂ ↦ (f w : ℂ)) z

namespace LocalUpperHalfPlaneMapHolomorphicOn

/-- Pointwise `HasDerivAt` data gives the local holomorphicity predicate. -/
theorem of_hasDerivAt {U : Set ℂ} {f : ℂ → ℍ} {f' : ℂ → ℂ}
    (h :
      ∀ z, z ∈ U →
        HasDerivAt (fun w : ℂ ↦ (f w : ℂ)) (f' z) z) :
    LocalUpperHalfPlaneMapHolomorphicOn U f := by
  intro z hz
  exact (h z hz).differentiableAt

end LocalUpperHalfPlaneMapHolomorphicOn

/--
A local upper-half-plane developing map refining a local projective developing
map in the hyperbolic case.

The projective Schwarzian construction naturally gives a finite
Riemann-sphere-valued map.  To recover the hyperbolic developing map one must
add two extra pieces of data: the finite affine coordinate lands in `ℍ`, and it
pulls the squared-density `exp (2u)` back from the Poincare density by
`|f'|^2 / (Im f)^2`.
-/
structure LocalUpperHalfPlaneDevelopingMap {u : LocalConformalFactor}
    (S : LocalSchwarzianData u) where
  /-- The underlying finite projective developing map. -/
  projective : LocalProjectiveDevelopingMap S
  /-- The same affine coordinate, now regarded as upper-half-plane-valued. -/
  upperHalfPlaneMap : ℂ → ℍ
  /-- The upper-half-plane branch agrees with the affine projective coordinate. -/
  upperHalfPlaneMap_eq_affine :
    ∀ z, z ∈ projective.domain → (upperHalfPlaneMap z : ℂ) = projective.affineMap z
  /-- The upper-half-plane branch is holomorphic on the local domain. -/
  holomorphic_on_domain :
    LocalUpperHalfPlaneMapHolomorphicOn projective.domain upperHalfPlaneMap
  /-- The symbolic derivative in the projective package is the actual derivative. -/
  deriv_eq_projectiveDeriv :
    ∀ z, z ∈ projective.domain → deriv projective.affineMap z = projective.affineMapDeriv z
  /-- The actual derivative of the upper-half-plane branch is the projective derivative. -/
  upperHalfPlane_deriv_eq_projectiveDeriv :
    ∀ z, z ∈ projective.domain →
      deriv (fun w : ℂ ↦ (upperHalfPlaneMap w : ℂ)) z = projective.affineMapDeriv z
  /--
  Poincare pullback formula for the squared conformal density:
  `exp (2u) = |f'|^2 / (Im f)^2`.
  -/
  densitySq_eq_pullback :
    ∀ z, z ∈ projective.domain →
      u.densitySq z =
        Complex.normSq (projective.affineMapDeriv z) / ((upperHalfPlaneMap z : ℂ).im ^ 2)

namespace LocalUpperHalfPlaneDevelopingMap

/-- The domain of a local upper-half-plane developing map. -/
def domain {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) : Set ℂ :=
  H.projective.domain

/-- Restrict a local upper-half-plane developing map to an open subdomain. -/
def restrict {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (V : Set ℂ)
    (hVOpen : IsOpen V) (hVsub : V ⊆ H.domain) :
    LocalUpperHalfPlaneDevelopingMap S where
  projective := H.projective.restrict V hVOpen hVsub
  upperHalfPlaneMap := H.upperHalfPlaneMap
  upperHalfPlaneMap_eq_affine := fun z hz ↦
    H.upperHalfPlaneMap_eq_affine z (hVsub hz)
  holomorphic_on_domain := fun z hz ↦
    H.holomorphic_on_domain z (hVsub hz)
  deriv_eq_projectiveDeriv := fun z hz ↦
    H.deriv_eq_projectiveDeriv z (hVsub hz)
  upperHalfPlane_deriv_eq_projectiveDeriv := fun z hz ↦
    H.upperHalfPlane_deriv_eq_projectiveDeriv z (hVsub hz)
  densitySq_eq_pullback := fun z hz ↦
    H.densitySq_eq_pullback z (hVsub hz)

@[simp]
theorem restrict_domain {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (V : Set ℂ)
    (hVOpen : IsOpen V) (hVsub : V ⊆ H.domain) :
    (H.restrict V hVOpen hVsub).domain = V :=
  rfl

/-- The complex-valued upper-half-plane branch is differentiable at every domain point. -/
theorem differentiableAt_upperHalfPlaneMap
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) {z : ℂ} (hz : z ∈ H.domain) :
    DifferentiableAt ℂ (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z :=
  H.holomorphic_on_domain z hz

/--
Two local upper-half-plane developing maps have a real Mobius transition on
their overlap.

This is the local form of the real-holonomy statement: once Schwarzian ODE
solutions have been normalized to recover the same hyperbolic metric as
`ℍ`-valued maps, their coordinate change should be an orientation-preserving
isometry of the upper half-plane, hence an element of `PSL(2, ℝ)`.
-/
def HasRealMobiusTransition
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂) : Prop :=
  ∃ A : RealMobiusRepresentative,
    ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
      H₂.upperHalfPlaneMap z =
        realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z)

/--
A pointed real Mobius transition at one base point.

This records the value and complex derivative of the postcomposed first branch
at the base point.  It is the formal local one-jet version of the geometric
fact that an orientation-preserving hyperbolic isometry is determined by its
value and tangent direction at one point.
-/
def HasPointedRealMobiusTransition
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ) : Prop :=
  z₀ ∈ H₁.domain ∧ z₀ ∈ H₂.domain ∧
    H₂.upperHalfPlaneMap z₀ =
      realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z₀) ∧
    deriv (fun z : ℂ ↦ (H₂.upperHalfPlaneMap z : ℂ)) z₀ =
      deriv
        (fun z : ℂ ↦ (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) : ℂ))
        z₀

/-- Every upper-half-plane branch has the identity real-Mobius transition to itself. -/
theorem hasRealMobiusTransition_self
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) :
    H.HasRealMobiusTransition H := by
  refine ⟨1, ?_⟩
  intro z _hz _hz'
  simp [realMobiusRepresentativeAction_one]

/-- Real-Mobius transition data restricts to smaller branch domains. -/
theorem HasRealMobiusTransition.restrict
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    {H₁ : LocalUpperHalfPlaneDevelopingMap S₁}
    {H₂ : LocalUpperHalfPlaneDevelopingMap S₂}
    (h : H₁.HasRealMobiusTransition H₂)
    (V₁ V₂ : Set ℂ) (hV₁Open : IsOpen V₁) (hV₂Open : IsOpen V₂)
    (hV₁sub : V₁ ⊆ H₁.domain) (hV₂sub : V₂ ⊆ H₂.domain) :
    (H₁.restrict V₁ hV₁Open hV₁sub).HasRealMobiusTransition
      (H₂.restrict V₂ hV₂Open hV₂sub) := by
  rcases h with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  intro z hz₁ hz₂
  exact hA z (hV₁sub hz₁) (hV₂sub hz₂)

/-- Forget the upper-half-plane branch and keep the projective developing map. -/
def toLocalProjectiveDevelopingMap
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) :
    LocalProjectiveDevelopingMap S :=
  H.projective

/-- The affine coordinate has positive imaginary part on the local domain. -/
theorem affineMap_im_pos
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) {z : ℂ}
    (hz : z ∈ H.domain) :
    0 < (H.projective.affineMap z).im := by
  rw [← H.upperHalfPlaneMap_eq_affine z hz]
  exact (H.upperHalfPlaneMap z).im_pos

/-- The squared norm of the projective derivative is positive on the domain. -/
theorem affineDerivativeNormSq_pos
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) {z : ℂ}
    (hz : z ∈ H.domain) :
    0 < Complex.normSq (H.projective.affineMapDeriv z) :=
  Complex.normSq_pos.mpr (H.projective.affineMapDeriv_ne_zero z hz)

/-- The actual derivative norm square of the `ℍ`-branch is positive. -/
theorem upperHalfPlaneDerivativeNormSq_pos
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) {z : ℂ}
    (hz : z ∈ H.domain) :
    0 < complexDerivativeNormSq H.upperHalfPlaneMap z := by
  rw [complexDerivativeNormSq, H.upperHalfPlane_deriv_eq_projectiveDeriv z hz]
  exact H.affineDerivativeNormSq_pos hz

/--
The squared hyperbolic norm of the derivative of an upper-half-plane branch.

This is the infinitesimal Poincare norm of the tangent vector determined by
the complex derivative.
-/
def hyperbolicDerivativeNormSqAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (z : ℂ) : ℝ :=
  complexDerivativeNormSq H.upperHalfPlaneMap z / ((H.upperHalfPlaneMap z : ℂ).im ^ 2)

/--
For a metric-recovering branch, the hyperbolic norm square of the derivative
is the conformal density square.
-/
theorem hyperbolicDerivativeNormSqAt_eq_densitySq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) {z : ℂ}
    (hz : z ∈ H.domain) :
    H.hyperbolicDerivativeNormSqAt z = u.densitySq z := by
  rw [hyperbolicDerivativeNormSqAt, complexDerivativeNormSq,
    H.upperHalfPlane_deriv_eq_projectiveDeriv z hz]
  exact (H.densitySq_eq_pullback z hz).symm

/--
Two metric-recovering branches for the same conformal factor have equal
hyperbolic derivative norm square at every common point.
-/
theorem hyperbolicDerivativeNormSqAt_eq_of_mem_inter
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂) {z : ℂ}
    (hz₁ : z ∈ H₁.domain) (hz₂ : z ∈ H₂.domain) :
    H₁.hyperbolicDerivativeNormSqAt z =
      H₂.hyperbolicDerivativeNormSqAt z := by
  rw [H₁.hyperbolicDerivativeNormSqAt_eq_densitySq hz₁,
    H₂.hyperbolicDerivativeNormSqAt_eq_densitySq hz₂]

/-- The Poincare denominator `(Im f)^2` is positive on the local domain. -/
theorem affineMap_im_sq_pos
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) {z : ℂ}
    (hz : z ∈ H.domain) :
    0 < (H.projective.affineMap z).im ^ 2 :=
  sq_pos_of_pos (H.affineMap_im_pos hz)

/-- The density pullback formula rewritten using only the affine coordinate. -/
theorem densitySq_eq_pullback_affine
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) {z : ℂ}
    (hz : z ∈ H.domain) :
    u.densitySq z =
      Complex.normSq (H.projective.affineMapDeriv z) /
        ((H.projective.affineMap z).im ^ 2) := by
  rw [H.densitySq_eq_pullback z hz]
  rw [← H.upperHalfPlaneMap_eq_affine z hz]

/--
Turn a local upper-half-plane developing map into the existing coordinate
Poincare pullback formula over the coordinate domain, provided the ambient
metric density agrees with the conformal factor on that domain.
-/
def toCoordinateUpperHalfPlanePullbackFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (g : HyperbolicMetric ℂ)
    (hMetric : ∀ z, z ∈ H.domain →
      g.toConformalMetric.densitySqInChart (OpenPartialHomeomorph.refl ℂ) (by simp) z =
        u.densitySq z) :
    CoordinateUpperHalfPlanePullbackFormula ℂ g where
  domain := H.domain
  isOpen_domain := H.projective.isOpen_domain
  coordinateDomain := H.domain
  isOpen_coordinateDomain := H.projective.isOpen_domain
  coordinate := id
  chart := OpenPartialHomeomorph.refl ℂ
  chart_mem_atlas := by
    simp
  domain_subset_chart_source := by
    intro z _hz
    simp
  coordinate_eq_chart := by
    intro z _hz
    rfl
  coordinate_mem_domain := by
    intro z hz
    exact hz
  localMap := H.upperHalfPlaneMap
  regularity := {
    holomorphic_on_coordinateDomain := H.holomorphic_on_domain
    local_biholomorph_on_domain :=
      by
        intro z hz
        rw [H.upperHalfPlane_deriv_eq_projectiveDeriv z hz]
        exact H.projective.affineMapDeriv_ne_zero z hz }
  derivative_ne_zero_on_domain := by
    intro z hz
    change deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z ≠ 0
    rw [H.upperHalfPlane_deriv_eq_projectiveDeriv z hz]
    exact H.projective.affineMapDeriv_ne_zero z hz
  densitySqInChart_eq_pullback := by
    intro z hz
    calc
      g.toConformalMetric.densitySqInChart (OpenPartialHomeomorph.refl ℂ) (by simp) (id z)
          = u.densitySq z := hMetric z hz
      _ =
          Complex.normSq (H.projective.affineMapDeriv z) /
            ((H.upperHalfPlaneMap z : ℂ).im ^ 2) :=
          H.densitySq_eq_pullback z hz
      _ =
          complexDerivativeNormSq H.upperHalfPlaneMap (id z) /
            ((H.upperHalfPlaneMap (id z) : ℂ).im ^ 2) := by
          simp [complexDerivativeNormSq, H.upperHalfPlane_deriv_eq_projectiveDeriv z hz]

/--
Turn a local upper-half-plane Schwarzian branch into a local Liouville
developing solution on its own domain.

The conformal factor is restricted to the branch domain, which is why this
constructs the stronger `LocalLiouvilleDevelopingSolution` package rather than
only the coordinate pullback formula.
-/
def toLocalLiouvilleDevelopingSolution
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (g : HyperbolicMetric ℂ)
    (hu : u.SolvesLiouvilleEquation)
    (hMetric : ∀ z, z ∈ H.domain →
      g.toConformalMetric.densitySqInChart (OpenPartialHomeomorph.refl ℂ) (by simp) z =
        u.densitySq z) :
    LocalLiouvilleDevelopingSolution ℂ g where
  pullbackFormula := H.toCoordinateUpperHalfPlanePullbackFormula g hMetric
  conformalFactor :=
    u.restrict H.domain H.projective.isOpen_domain H.projective.domain_subset
  coordinateDomain_eq := rfl
  chart := OpenPartialHomeomorph.refl ℂ
  chart_mem_atlas := by
    simp
  domain_subset_chart_source := by
    intro z _hz
    simp
  coordinate_eq_chart := by
    intro z _hz
    rfl
  solves_liouville :=
    u.restrict_solvesLiouvilleEquation H.domain H.projective.isOpen_domain
      H.projective.domain_subset hu
  densitySqInChart_eq_conformalFactor := by
    intro z hz
    calc
      g.toConformalMetric.densitySqInChart (OpenPartialHomeomorph.refl ℂ) (by simp) (id z)
          = u.densitySq z := hMetric z hz
      _ =
          (u.restrict H.domain H.projective.isOpen_domain H.projective.domain_subset).densitySq
            ((H.toCoordinateUpperHalfPlanePullbackFormula g hMetric).coordinate z) := by
        rfl
  densitySqInChart_eq_pullback :=
    (H.toCoordinateUpperHalfPlanePullbackFormula g hMetric).densitySqInChart_eq_pullback

/--
Turn a coordinate upper-half-plane Schwarzian branch into a local Liouville
developing solution for a surface chart whose coordinate image lies in the
branch domain.

This is the chartwise version of `toLocalLiouvilleDevelopingSolution`: the
surface domain and coordinate come from an existing local Liouville metric
formula, while the conformal factor is restricted to the chosen Schwarzian
branch domain.
-/
def toLocalLiouvilleDevelopingSolutionOfMetricFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {S : LocalSchwarzianData F.conformalFactor}
    (H : LocalUpperHalfPlaneDevelopingMap S)
    (hImage : ∀ x, x ∈ F.domain → F.coordinate x ∈ H.domain) :
    LocalLiouvilleDevelopingSolution X g where
  pullbackFormula :=
    { domain := F.domain
      isOpen_domain := F.isOpen_domain
      coordinateDomain := H.domain
      isOpen_coordinateDomain := H.projective.isOpen_domain
      coordinate := F.coordinate
      chart := F.chart
      chart_mem_atlas := F.chart_mem_atlas
      domain_subset_chart_source := F.domain_subset_chart_source
      coordinate_eq_chart := F.coordinate_eq_chart
      coordinate_mem_domain := hImage
      localMap := H.upperHalfPlaneMap
      regularity := {
        holomorphic_on_coordinateDomain := H.holomorphic_on_domain
        local_biholomorph_on_domain :=
          by
            intro z hz
            rw [H.upperHalfPlane_deriv_eq_projectiveDeriv z hz]
            exact H.projective.affineMapDeriv_ne_zero z hz }
      derivative_ne_zero_on_domain := by
        intro x hx
        rw [H.upperHalfPlane_deriv_eq_projectiveDeriv (F.coordinate x) (hImage x hx)]
        exact H.projective.affineMapDeriv_ne_zero (F.coordinate x) (hImage x hx)
      densitySqInChart_eq_pullback := by
        intro x hx
        calc
          g.toConformalMetric.densitySqInChart F.chart F.chart_mem_atlas (F.coordinate x) =
              F.conformalFactor.densitySq (F.coordinate x) :=
            F.densitySqInChart_eq_conformalFactor x hx
          _ =
              Complex.normSq (H.projective.affineMapDeriv (F.coordinate x)) /
                ((H.upperHalfPlaneMap (F.coordinate x) : ℂ).im ^ 2) :=
            H.densitySq_eq_pullback (F.coordinate x) (hImage x hx)
          _ =
              complexDerivativeNormSq H.upperHalfPlaneMap (F.coordinate x) /
                ((H.upperHalfPlaneMap (F.coordinate x) : ℂ).im ^ 2) := by
            simp [complexDerivativeNormSq,
              H.upperHalfPlane_deriv_eq_projectiveDeriv (F.coordinate x) (hImage x hx)]
    }
  conformalFactor :=
    F.conformalFactor.restrict H.domain H.projective.isOpen_domain
      H.projective.domain_subset
  coordinateDomain_eq := rfl
  chart := F.chart
  chart_mem_atlas := F.chart_mem_atlas
  domain_subset_chart_source := F.domain_subset_chart_source
  coordinate_eq_chart := F.coordinate_eq_chart
  solves_liouville :=
    F.conformalFactor.restrict_solvesLiouvilleEquation H.domain
      H.projective.isOpen_domain H.projective.domain_subset F.solves_liouville
  densitySqInChart_eq_conformalFactor := by
    intro x hx
    simpa [LocalConformalFactor.restrict_densitySq]
      using F.densitySqInChart_eq_conformalFactor x hx
  densitySqInChart_eq_pullback := by
    intro x hx
    calc
      g.toConformalMetric.densitySqInChart F.chart F.chart_mem_atlas (F.coordinate x) =
          F.conformalFactor.densitySq (F.coordinate x) :=
        F.densitySqInChart_eq_conformalFactor x hx
      _ =
          Complex.normSq (H.projective.affineMapDeriv (F.coordinate x)) /
            ((H.upperHalfPlaneMap (F.coordinate x) : ℂ).im ^ 2) :=
        H.densitySq_eq_pullback (F.coordinate x) (hImage x hx)
      _ =
          complexDerivativeNormSq H.upperHalfPlaneMap (F.coordinate x) /
            ((H.upperHalfPlaneMap (F.coordinate x) : ℂ).im ^ 2) := by
        simp [complexDerivativeNormSq,
          H.upperHalfPlane_deriv_eq_projectiveDeriv (F.coordinate x) (hImage x hx)]

end LocalUpperHalfPlaneDevelopingMap

/--
Surface-level Schwarzian branch data over a local Liouville metric-formula
atlas.

For every surface point `x`, this chooses a Schwarzian coefficient for the
local conformal factor in the metric formula at `x`, an `ℍ`-valued branch of a
Schwarzian solution, and a proof that the surface chart image lies in that
branch domain.  The last field records the real Mobius transition compatibility
needed by the existing `LocalLiouvilleDevelopingSolutionAtlas` interface.
-/
structure SurfaceSchwarzianBranchData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} (A : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- The Schwarzian data chosen over the local metric formula at `x`. -/
  schwarzianAt : ∀ x : X, LocalSchwarzianData (A.formulaAt x).conformalFactor
  /-- The upper-half-plane branch chosen over the local metric formula at `x`. -/
  branchAt : ∀ x : X, LocalUpperHalfPlaneDevelopingMap (schwarzianAt x)
  /-- The coordinate image of the surface chart lies in the branch domain. -/
  coordinate_image_subset :
    ∀ x y : X, y ∈ (A.formulaAt x).domain →
      (A.formulaAt x).coordinate y ∈ (branchAt x).domain
  /-- The resulting surface local charts have real Mobius transitions. -/
  transition_realMobius :
    ∀ x y : X,
      (((branchAt x).toLocalLiouvilleDevelopingSolutionOfMetricFormula
        (coordinate_image_subset x)).toHyperbolicLocalChart).HasRealMobiusTransition
      (((branchAt y).toLocalLiouvilleDevelopingSolutionOfMetricFormula
        (coordinate_image_subset y)).toHyperbolicLocalChart)

namespace SurfaceSchwarzianBranchData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {A : LocalLiouvilleMetricFormulaAtlas X g}

/-- The local Liouville developing solution produced near `x`. -/
def solutionAt (B : SurfaceSchwarzianBranchData A) (x : X) :
    LocalLiouvilleDevelopingSolution X g :=
  (B.branchAt x).toLocalLiouvilleDevelopingSolutionOfMetricFormula
    (B.coordinate_image_subset x)

/--
Assemble surface-level Schwarzian branch data into the standard local
Liouville developing-solution atlas.
-/
def toLocalLiouvilleDevelopingSolutionAtlas
    (B : SurfaceSchwarzianBranchData A) :
    LocalLiouvilleDevelopingSolutionAtlas X g where
  solutionAt := B.solutionAt
  mem_solutionAt_domain := A.mem_formulaAt_domain
  transition_realMobius := B.transition_realMobius

/-- Surface-level Schwarzian branch data gives the metric-level local solving target. -/
theorem hasLocalLiouvilleDevelopingSolutionAtlas
    (B : SurfaceSchwarzianBranchData A) :
    g.HasLocalLiouvilleDevelopingSolutionAtlas :=
  ⟨B.toLocalLiouvilleDevelopingSolutionAtlas⟩

/-- Surface-level Schwarzian branch data gives coordinate Poincare pullback formulas. -/
theorem hasCoordinateUpperHalfPlanePullbackFormulaAtlas
    (B : SurfaceSchwarzianBranchData A) :
    g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas :=
  HyperbolicMetric.hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasLocalLiouvilleDevelopingSolutionAtlas
    B.hasLocalLiouvilleDevelopingSolutionAtlas

/-- Surface-level Schwarzian branch data gives local upper-half-plane models. -/
theorem hasUpperHalfPlaneLocalModels
    (B : SurfaceSchwarzianBranchData A) :
    g.HasUpperHalfPlaneLocalModels :=
  HyperbolicMetric.hasUpperHalfPlaneLocalModels_of_hasLocalLiouvilleDevelopingSolutionAtlas
    B.hasLocalLiouvilleDevelopingSolutionAtlas

end SurfaceSchwarzianBranchData

/--
Pointed surface-level Schwarzian branch data.

This is the local output shape of the Schwarzian ODE solver: near each surface
point `x`, it chooses an upper-half-plane branch defined at the coordinate of
`x`.  Unlike `SurfaceSchwarzianBranchData`, it does not require the original
surface chart image to lie in the branch domain.  Instead, it records the
openness needed to shrink the surface formula to the part whose coordinate
lies in the branch domain.
-/
structure SurfaceSchwarzianPointedBranchPreData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} (A : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- The Schwarzian data chosen over the local metric formula at `x`. -/
  schwarzianAt : ∀ x : X, LocalSchwarzianData (A.formulaAt x).conformalFactor
  /-- The upper-half-plane branch chosen over the local metric formula at `x`. -/
  branchAt : ∀ x : X, LocalUpperHalfPlaneDevelopingMap (schwarzianAt x)
  /-- The branch chosen at `x` is defined at the coordinate of `x`. -/
  center_mem_branch :
    ∀ x : X, (A.formulaAt x).coordinate x ∈ (branchAt x).domain
  /--
  The surface domain obtained by keeping only points whose coordinates lie in
  the branch domain is open.

  This is explicit because the lightweight local formula records only a bare
  coordinate function.  Once these formulas are tied to `ChartedSpace` charts,
  this should follow from continuity and openness of branch domains.
  -/
  restricted_domain_open :
    ∀ x : X, IsOpen
      {y : X | y ∈ (A.formulaAt x).domain ∧
        (A.formulaAt x).coordinate y ∈ (branchAt x).domain}

namespace SurfaceSchwarzianPointedBranchPreData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {A : LocalLiouvilleMetricFormulaAtlas X g}

/--
The metric formula at `x`, restricted to the surface points whose coordinates
lie in the chosen local branch domain.
-/
def restrictedFormulaAt
    (B : SurfaceSchwarzianPointedBranchPreData A) (x : X) :
    LocalLiouvilleMetricFormula X g :=
  (A.formulaAt x).restrictDomainToCoordinateSubset (B.branchAt x).domain
    (B.branchAt x).projective.domain_subset (B.restricted_domain_open x)

@[simp]
theorem restrictedFormulaAt_domain
    (B : SurfaceSchwarzianPointedBranchPreData A) (x : X) :
    (B.restrictedFormulaAt x).domain =
      {y : X | y ∈ (A.formulaAt x).domain ∧
        (A.formulaAt x).coordinate y ∈ (B.branchAt x).domain} :=
  rfl

@[simp]
theorem restrictedFormulaAt_conformalFactor
    (B : SurfaceSchwarzianPointedBranchPreData A) (x : X) :
    (B.restrictedFormulaAt x).conformalFactor =
      (A.formulaAt x).conformalFactor :=
  rfl

/--
Shrink every metric formula in the atlas to the branch domain chosen at its
base point.
-/
def toRestrictedMetricFormulaAtlas
    (B : SurfaceSchwarzianPointedBranchPreData A) :
    LocalLiouvilleMetricFormulaAtlas X g where
  formulaAt := B.restrictedFormulaAt
  mem_formulaAt_domain := by
    intro x
    exact ⟨A.mem_formulaAt_domain x, B.center_mem_branch x⟩

/-- The local Liouville developing solution on the restricted formula at `x`. -/
def solutionAt
    (B : SurfaceSchwarzianPointedBranchPreData A) (x : X) :
    LocalLiouvilleDevelopingSolution X g :=
  (B.branchAt x).toLocalLiouvilleDevelopingSolutionOfMetricFormula
    (F := B.restrictedFormulaAt x) (by
      intro y hy
      exact hy.2)

/--
Pointed branch data plus real-Mobius transition compatibility on the restricted
surface domains gives the stronger atlas-level branch data.
-/
def toSurfaceSchwarzianBranchData
    (B : SurfaceSchwarzianPointedBranchPreData A)
    (hTransition :
      ∀ x y : X,
        ((B.solutionAt x).toHyperbolicLocalChart).HasRealMobiusTransition
          ((B.solutionAt y).toHyperbolicLocalChart)) :
    SurfaceSchwarzianBranchData B.toRestrictedMetricFormulaAtlas where
  schwarzianAt := B.schwarzianAt
  branchAt := B.branchAt
  coordinate_image_subset := by
    intro x y hy
    exact hy.2
  transition_realMobius := by
    intro x y
    exact hTransition x y

/--
Pointed branch data with real-Mobius transitions gives a local Liouville
developing-solution atlas after shrinking the surface domains.
-/
def toLocalLiouvilleDevelopingSolutionAtlas
    (B : SurfaceSchwarzianPointedBranchPreData A)
    (hTransition :
      ∀ x y : X,
        ((B.solutionAt x).toHyperbolicLocalChart).HasRealMobiusTransition
          ((B.solutionAt y).toHyperbolicLocalChart)) :
    LocalLiouvilleDevelopingSolutionAtlas X g :=
  (B.toSurfaceSchwarzianBranchData hTransition).toLocalLiouvilleDevelopingSolutionAtlas

/--
Pointed branch data with real-Mobius transitions gives local upper-half-plane
models after shrinking the surface domains.
-/
theorem hasUpperHalfPlaneLocalModels
    (B : SurfaceSchwarzianPointedBranchPreData A)
    (hTransition :
      ∀ x y : X,
        ((B.solutionAt x).toHyperbolicLocalChart).HasRealMobiusTransition
          ((B.solutionAt y).toHyperbolicLocalChart)) :
    g.HasUpperHalfPlaneLocalModels :=
  (B.toSurfaceSchwarzianBranchData hTransition).hasUpperHalfPlaneLocalModels

end SurfaceSchwarzianPointedBranchPreData

/--
Pointed surface-level Schwarzian branch data with real-Mobius transition
compatibility after shrinking the surface domains.
-/
structure SurfaceSchwarzianPointedBranchData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} (A : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- The pointed local branch choices and shrinking data. -/
  preData : SurfaceSchwarzianPointedBranchPreData A
  /-- The resulting restricted local charts have real Mobius transitions. -/
  transition_realMobius :
    ∀ x y : X,
      ((preData.solutionAt x).toHyperbolicLocalChart).HasRealMobiusTransition
        ((preData.solutionAt y).toHyperbolicLocalChart)

namespace SurfaceSchwarzianPointedBranchData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {A : LocalLiouvilleMetricFormulaAtlas X g}

/-- The metric formula atlas obtained by shrinking to the pointed branch domains. -/
def toRestrictedMetricFormulaAtlas
    (B : SurfaceSchwarzianPointedBranchData A) :
    LocalLiouvilleMetricFormulaAtlas X g :=
  B.preData.toRestrictedMetricFormulaAtlas

/-- The local Liouville developing solution on the restricted formula at `x`. -/
def solutionAt
    (B : SurfaceSchwarzianPointedBranchData A) (x : X) :
    LocalLiouvilleDevelopingSolution X g :=
  B.preData.solutionAt x

/-- Convert pointed branch data into ordinary branch data over the restricted atlas. -/
def toSurfaceSchwarzianBranchData
    (B : SurfaceSchwarzianPointedBranchData A) :
    SurfaceSchwarzianBranchData B.toRestrictedMetricFormulaAtlas :=
  B.preData.toSurfaceSchwarzianBranchData B.transition_realMobius

/--
Pointed branch data gives a local Liouville developing-solution atlas after
shrinking the surface domains.
-/
def toLocalLiouvilleDevelopingSolutionAtlas
    (B : SurfaceSchwarzianPointedBranchData A) :
    LocalLiouvilleDevelopingSolutionAtlas X g :=
  B.toSurfaceSchwarzianBranchData.toLocalLiouvilleDevelopingSolutionAtlas

/--
Pointed branch data gives local upper-half-plane models after shrinking the
surface domains.
-/
theorem hasUpperHalfPlaneLocalModels
    (B : SurfaceSchwarzianPointedBranchData A) :
    g.HasUpperHalfPlaneLocalModels :=
  B.toSurfaceSchwarzianBranchData.hasUpperHalfPlaneLocalModels

end SurfaceSchwarzianPointedBranchData

/--
An atlas of local upper-half-plane branches over one conformal coordinate
domain.

This forgets how the branches were constructed.  It remembers only that every
point in the coordinate domain is covered by an `ℍ`-valued branch and that
overlaps are preconnected, which is the shape needed before asking for real
Mobius transition maps.
-/
structure LocalUpperHalfPlaneBranchAtlas (u : LocalConformalFactor) where
  /-- The Schwarzian data attached to the branch chosen near each point. -/
  schwarzianAt : u.coordinateDomain → LocalSchwarzianData u
  /-- The upper-half-plane branch chosen near each point. -/
  branchAt : ∀ z : u.coordinateDomain, LocalUpperHalfPlaneDevelopingMap (schwarzianAt z)
  /-- The chosen branch at `z` is defined at `z`. -/
  mem_branchAt_domain : ∀ z : u.coordinateDomain, (z : ℂ) ∈ (branchAt z).domain
  /-- The pairwise overlaps of chosen branches are preconnected. -/
  overlap_preconnected :
    ∀ z w : u.coordinateDomain, IsPreconnected
      ((branchAt z).domain ∩ (branchAt w).domain)

namespace LocalUpperHalfPlaneBranchAtlas

/-- The branch chosen near a point, with a shorter name. -/
def branchNear {u : LocalConformalFactor}
    (A : LocalUpperHalfPlaneBranchAtlas u) (z : u.coordinateDomain) :
    LocalUpperHalfPlaneDevelopingMap (A.schwarzianAt z) :=
  A.branchAt z

/-- The chosen local branches cover the coordinate domain. -/
theorem mem_branchNear_domain {u : LocalConformalFactor}
    (A : LocalUpperHalfPlaneBranchAtlas u) (z : u.coordinateDomain) :
    (z : ℂ) ∈ (A.branchNear z).domain :=
  A.mem_branchAt_domain z

/--
Data for shrinking every branch in a local upper-half-plane branch atlas.

The shrunk branch around `z` must remain an open neighborhood of `z`, lie
inside the original branch domain, and have preconnected pairwise overlaps.
-/
structure ShrinkData {u : LocalConformalFactor}
    (A : LocalUpperHalfPlaneBranchAtlas u) where
  /-- The chosen smaller coordinate domain around each base point. -/
  domainAt : u.coordinateDomain → Set ℂ
  /-- Each chosen coordinate domain is open. -/
  isOpen_domainAt : ∀ z : u.coordinateDomain, IsOpen (domainAt z)
  /-- Each chosen domain lies in the original branch domain. -/
  domainAt_subset :
    ∀ z : u.coordinateDomain, domainAt z ⊆ (A.branchNear z).domain
  /-- Each chosen domain still contains its base point. -/
  mem_domainAt : ∀ z : u.coordinateDomain, (z : ℂ) ∈ domainAt z
  /-- The pairwise overlaps of the chosen domains are preconnected. -/
  overlap_preconnected :
    ∀ z w : u.coordinateDomain, IsPreconnected (domainAt z ∩ domainAt w)

/--
Ball-shaped data for shrinking every branch in a local upper-half-plane branch
atlas.

This is the geometric form usually produced by local coordinate shrinking.  The
ordinary `ShrinkData` overlap condition is then automatic, because intersections
of balls in `ℂ` are convex and hence preconnected.
-/
structure BallShrinkData {u : LocalConformalFactor}
    (A : LocalUpperHalfPlaneBranchAtlas u) where
  /-- The radius of the smaller ball around each base point. -/
  radiusAt : u.coordinateDomain → ℝ
  /-- Every chosen radius is positive, so the base point remains covered. -/
  radius_pos : ∀ z : u.coordinateDomain, 0 < radiusAt z
  /-- Each chosen ball lies in the original branch domain. -/
  ball_subset :
    ∀ z : u.coordinateDomain,
      Metric.ball (z : ℂ) (radiusAt z) ⊆ (A.branchNear z).domain

namespace BallShrinkData

/-- Ball-shaped shrink data gives ordinary shrink data. -/
def toShrinkData {u : LocalConformalFactor}
    {A : LocalUpperHalfPlaneBranchAtlas u} (D : A.BallShrinkData) :
    A.ShrinkData where
  domainAt := fun z ↦ Metric.ball (z : ℂ) (D.radiusAt z)
  isOpen_domainAt := fun _ ↦ Metric.isOpen_ball
  domainAt_subset := D.ball_subset
  mem_domainAt := fun z ↦ Metric.mem_ball_self (D.radius_pos z)
  overlap_preconnected := by
    intro z w
    exact
      ((convex_ball (z : ℂ) (D.radiusAt z)).inter
        (convex_ball (w : ℂ) (D.radiusAt w))).isPreconnected

@[simp]
theorem toShrinkData_domainAt {u : LocalConformalFactor}
    {A : LocalUpperHalfPlaneBranchAtlas u} (D : A.BallShrinkData)
    (z : u.coordinateDomain) :
    D.toShrinkData.domainAt z = Metric.ball (z : ℂ) (D.radiusAt z) :=
  rfl

end BallShrinkData

/--
Every chosen branch admits a positive coordinate ball around its base point
inside its domain.
-/
theorem exists_ball_subset_branchNear_domain {u : LocalConformalFactor}
    (A : LocalUpperHalfPlaneBranchAtlas u) (z : u.coordinateDomain) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (z : ℂ) r ⊆ (A.branchNear z).domain := by
  exact
    Metric.mem_nhds_iff.mp
      (by
        simpa [LocalUpperHalfPlaneDevelopingMap.domain] using
          (A.branchNear z).projective.isOpen_domain.mem_nhds
            (A.mem_branchNear_domain z))

/--
Canonical ball-shrink data obtained from openness of the branch domains.

This discharges the analytic "fit a ball inside the branch domain" part of the
charted-overlap selection problem.  The later surface-good-cover step may still
choose different ball radii if needed.
-/
noncomputable def ballShrinkData {u : LocalConformalFactor}
    (A : LocalUpperHalfPlaneBranchAtlas u) :
    A.BallShrinkData where
  radiusAt := fun z ↦
    Classical.choose (A.exists_ball_subset_branchNear_domain z)
  radius_pos := fun z ↦
    (Classical.choose_spec (A.exists_ball_subset_branchNear_domain z)).1
  ball_subset := fun z ↦
    (Classical.choose_spec (A.exists_ball_subset_branchNear_domain z)).2

/-- Every local branch atlas has ball-shaped shrink data. -/
theorem nonempty_ballShrinkData {u : LocalConformalFactor}
    (A : LocalUpperHalfPlaneBranchAtlas u) :
    Nonempty A.BallShrinkData :=
  ⟨A.ballShrinkData⟩

/-- Restrict every branch in a local branch atlas using `ShrinkData`. -/
def shrink {u : LocalConformalFactor}
    (A : LocalUpperHalfPlaneBranchAtlas u) (D : A.ShrinkData) :
    LocalUpperHalfPlaneBranchAtlas u where
  schwarzianAt := A.schwarzianAt
  branchAt := fun z ↦
    (A.branchNear z).restrict (D.domainAt z)
      (D.isOpen_domainAt z) (D.domainAt_subset z)
  mem_branchAt_domain := by
    intro z
    exact D.mem_domainAt z
  overlap_preconnected := by
    intro z w
    simpa [branchNear] using D.overlap_preconnected z w

@[simp]
theorem shrink_branchNear_domain {u : LocalConformalFactor}
    (A : LocalUpperHalfPlaneBranchAtlas u) (D : A.ShrinkData)
    (z : u.coordinateDomain) :
    ((A.shrink D).branchNear z).domain = D.domainAt z :=
  rfl

end LocalUpperHalfPlaneBranchAtlas

/--
A local upper-half-plane branch atlas with real Mobius transition maps on
overlaps.

This is the local, coordinate-domain version of the real-holonomy input used by
the global analytic-continuation pipeline.
-/
structure LocalRealUpperHalfPlaneBranchAtlas (u : LocalConformalFactor)
    extends LocalUpperHalfPlaneBranchAtlas u where
  /-- Any two chosen branches differ by a real Mobius transformation on overlap. -/
  transition_realMobius :
    ∀ z w : u.coordinateDomain,
      (toLocalUpperHalfPlaneBranchAtlas.branchNear z).HasRealMobiusTransition
        (toLocalUpperHalfPlaneBranchAtlas.branchNear w)

namespace LocalRealUpperHalfPlaneBranchAtlas

/-- Forget real-transition witnesses and retain only the underlying branch atlas. -/
def toBranchAtlas {u : LocalConformalFactor}
    (A : LocalRealUpperHalfPlaneBranchAtlas u) :
    LocalUpperHalfPlaneBranchAtlas u :=
  A.toLocalUpperHalfPlaneBranchAtlas

/-- Restrict every branch in a real branch atlas using `ShrinkData`. -/
def shrink {u : LocalConformalFactor}
    (A : LocalRealUpperHalfPlaneBranchAtlas u)
    (D : A.toBranchAtlas.ShrinkData) :
    LocalRealUpperHalfPlaneBranchAtlas u where
  toLocalUpperHalfPlaneBranchAtlas := A.toBranchAtlas.shrink D
  transition_realMobius := by
    intro z w
    exact
      (A.transition_realMobius z w).restrict
        (D.domainAt z) (D.domainAt w)
        (D.isOpen_domainAt z) (D.isOpen_domainAt w)
        (D.domainAt_subset z) (D.domainAt_subset w)

@[simp]
theorem shrink_branchNear_domain {u : LocalConformalFactor}
    (A : LocalRealUpperHalfPlaneBranchAtlas u)
    (D : A.toBranchAtlas.ShrinkData) (z : u.coordinateDomain) :
    ((A.shrink D).branchNear z).domain = D.domainAt z :=
  rfl

/--
When the conformal coordinate domain is all of `ℂ`, view a local real
upper-half-plane branch atlas as the existing coordinate-level Poincare
pullback formula atlas on `ℂ`.

The metric agreement hypothesis says that the ambient metric on `ℂ` has the
squared density encoded by the local conformal factor.  Each branch then gives
the usual formula `λ² = |f'|² / (Im f)²`, and the real Mobius transition
witnesses are exactly the transition witnesses required by
`CoordinateUpperHalfPlanePullbackFormulaAtlas`.
-/
def toCoordinateUpperHalfPlanePullbackFormulaAtlas {u : LocalConformalFactor}
    (A : LocalRealUpperHalfPlaneBranchAtlas u) (g : HyperbolicMetric ℂ)
    (hDomain : u.coordinateDomain = Set.univ)
    (hMetric :
      ∀ z, z ∈ u.coordinateDomain →
        g.toConformalMetric.densitySqInChart (OpenPartialHomeomorph.refl ℂ) (by simp) z =
          u.densitySq z) :
    CoordinateUpperHalfPlanePullbackFormulaAtlas ℂ g where
  formulaAt z :=
    let p : u.coordinateDomain := ⟨z, by rw [hDomain]; exact Set.mem_univ z⟩
    (A.branchNear p).toCoordinateUpperHalfPlanePullbackFormula g
      (fun w hw ↦ hMetric w ((A.branchNear p).projective.domain_subset hw))
  mem_formulaAt_domain := by
    intro z
    dsimp
    exact A.mem_branchNear_domain ⟨z, by rw [hDomain]; exact Set.mem_univ z⟩
  transition_realMobius := by
    intro z w
    let p : u.coordinateDomain := ⟨z, by rw [hDomain]; exact Set.mem_univ z⟩
    let q : u.coordinateDomain := ⟨w, by rw [hDomain]; exact Set.mem_univ w⟩
    rcases A.transition_realMobius p q with ⟨M, hM⟩
    exact ⟨M, by
      intro x hx hy
      exact hM x hx hy⟩

/--
When the conformal coordinate domain is all of `ℂ`, view a local real
upper-half-plane branch atlas as a local Liouville developing-solution atlas on
`ℂ`.
-/
def toLocalLiouvilleDevelopingSolutionAtlas {u : LocalConformalFactor}
    (A : LocalRealUpperHalfPlaneBranchAtlas u) (g : HyperbolicMetric ℂ)
    (hu : u.SolvesLiouvilleEquation)
    (hDomain : u.coordinateDomain = Set.univ)
    (hMetric :
      ∀ z, z ∈ u.coordinateDomain →
        g.toConformalMetric.densitySqInChart (OpenPartialHomeomorph.refl ℂ) (by simp) z =
          u.densitySq z) :
    LocalLiouvilleDevelopingSolutionAtlas ℂ g where
  solutionAt z :=
    let p : u.coordinateDomain := ⟨z, by rw [hDomain]; exact Set.mem_univ z⟩
    (A.branchNear p).toLocalLiouvilleDevelopingSolution g hu
      (fun w hw ↦ hMetric w ((A.branchNear p).projective.domain_subset hw))
  mem_solutionAt_domain := by
    intro z
    dsimp
    exact A.mem_branchNear_domain ⟨z, by rw [hDomain]; exact Set.mem_univ z⟩
  transition_realMobius := by
    intro z w
    let p : u.coordinateDomain := ⟨z, by rw [hDomain]; exact Set.mem_univ z⟩
    let q : u.coordinateDomain := ⟨w, by rw [hDomain]; exact Set.mem_univ w⟩
    rcases A.transition_realMobius p q with ⟨M, hM⟩
    exact ⟨M, by
      intro x hx hy
      exact hM x hx hy⟩

end LocalRealUpperHalfPlaneBranchAtlas

/--
Surface data obtained from real upper-half-plane branch atlases in each local
coordinate.

For every surface point `x`, this chooses a real branch atlas for the conformal
factor in the metric formula at `x`.  The branch used at `x` is the coordinate
branch centered at the base coordinate of `x`; the surface formula is then
shrunk to the points whose coordinates lie in that branch domain.
-/
structure SurfaceRealUpperHalfPlaneBranchAtlasPreData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} (A : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- A real upper-half-plane branch atlas in the coordinate attached to each `x`. -/
  realBranchAtlasAt :
    ∀ x : X, LocalRealUpperHalfPlaneBranchAtlas (A.formulaAt x).conformalFactor
  /--
  The surface domain obtained by pulling back the selected coordinate branch
  domain is open.
  -/
  restricted_domain_open :
    ∀ x : X, IsOpen
      {y : X | y ∈ (A.formulaAt x).domain ∧
        (A.formulaAt x).coordinate y ∈
          ((realBranchAtlasAt x).branchNear
            ⟨(A.formulaAt x).coordinate x,
              (A.formulaAt x).coordinate_mem_conformalFactor_domain x
                (A.mem_formulaAt_domain x)⟩).domain}

namespace SurfaceRealUpperHalfPlaneBranchAtlasPreData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {A : LocalLiouvilleMetricFormulaAtlas X g}

/-- The base coordinate of the formula centered at `x`. -/
def baseCoordinate
    (_B : SurfaceRealUpperHalfPlaneBranchAtlasPreData A) (x : X) :
    (A.formulaAt x).conformalFactor.coordinateDomain :=
  ⟨(A.formulaAt x).coordinate x,
    (A.formulaAt x).coordinate_mem_conformalFactor_domain x
      (A.mem_formulaAt_domain x)⟩

/-- The real coordinate branch atlas chosen at `x`. -/
def realBranchAtlas
    (B : SurfaceRealUpperHalfPlaneBranchAtlasPreData A) (x : X) :
    LocalRealUpperHalfPlaneBranchAtlas (A.formulaAt x).conformalFactor :=
  B.realBranchAtlasAt x

/-- The Schwarzian data of the selected branch at `x`. -/
def schwarzianAt
    (B : SurfaceRealUpperHalfPlaneBranchAtlasPreData A) (x : X) :
    LocalSchwarzianData (A.formulaAt x).conformalFactor :=
  (B.realBranchAtlas x).schwarzianAt (B.baseCoordinate x)

/-- The selected upper-half-plane branch at `x`. -/
def branchAt
    (B : SurfaceRealUpperHalfPlaneBranchAtlasPreData A) (x : X) :
    LocalUpperHalfPlaneDevelopingMap (B.schwarzianAt x) :=
  (B.realBranchAtlas x).branchNear (B.baseCoordinate x)

/-- The selected branch at `x` is defined at the coordinate of `x`. -/
theorem center_mem_branch
    (B : SurfaceRealUpperHalfPlaneBranchAtlasPreData A) (x : X) :
    (A.formulaAt x).coordinate x ∈ (B.branchAt x).domain :=
  (B.realBranchAtlas x).mem_branchNear_domain (B.baseCoordinate x)

/-- Convert coordinate real branch atlases into pointed surface branch predata. -/
def toSurfaceSchwarzianPointedBranchPreData
    (B : SurfaceRealUpperHalfPlaneBranchAtlasPreData A) :
    SurfaceSchwarzianPointedBranchPreData A where
  schwarzianAt := B.schwarzianAt
  branchAt := B.branchAt
  center_mem_branch := B.center_mem_branch
  restricted_domain_open := B.restricted_domain_open

/--
Coordinate real branch atlases plus surface real-Mobius compatibility of the
selected shrunk branches give pointed surface Schwarzian branch data.
-/
def toSurfaceSchwarzianPointedBranchData
    (B : SurfaceRealUpperHalfPlaneBranchAtlasPreData A)
    (hTransition :
      ∀ x y : X,
        HyperbolicLocalChart.HasRealMobiusTransition
          (((B.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
          (((B.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)) :
    SurfaceSchwarzianPointedBranchData A where
  preData := B.toSurfaceSchwarzianPointedBranchPreData
  transition_realMobius := hTransition

end SurfaceRealUpperHalfPlaneBranchAtlasPreData

/--
Surface real branch-atlas data with transition compatibility after shrinking.

This is a surface-level assembly package whose local input is coordinate
real-branch atlases, rather than raw individual branches.
-/
structure SurfaceRealUpperHalfPlaneBranchAtlasData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} (A : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- Coordinate real branch atlases and surface shrinking data. -/
  preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData A
  /-- The selected shrunk local surface charts have real Mobius transitions. -/
  transition_realMobius :
    ∀ x y : X,
      HyperbolicLocalChart.HasRealMobiusTransition
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)

namespace SurfaceRealUpperHalfPlaneBranchAtlasData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {A : LocalLiouvilleMetricFormulaAtlas X g}

/-- Forget to the pointed Schwarzian branch data used by the surface pipeline. -/
def toSurfaceSchwarzianPointedBranchData
    (B : SurfaceRealUpperHalfPlaneBranchAtlasData A) :
    SurfaceSchwarzianPointedBranchData A :=
  B.preData.toSurfaceSchwarzianPointedBranchData B.transition_realMobius

/-- Surface real branch-atlas data gives a local developing-solution atlas. -/
def toLocalLiouvilleDevelopingSolutionAtlas
    (B : SurfaceRealUpperHalfPlaneBranchAtlasData A) :
    LocalLiouvilleDevelopingSolutionAtlas X g :=
  B.toSurfaceSchwarzianPointedBranchData.toLocalLiouvilleDevelopingSolutionAtlas

/-- Surface real branch-atlas data gives local upper-half-plane models. -/
theorem hasUpperHalfPlaneLocalModels
    (B : SurfaceRealUpperHalfPlaneBranchAtlasData A) :
    g.HasUpperHalfPlaneLocalModels :=
  B.toSurfaceSchwarzianPointedBranchData.hasUpperHalfPlaneLocalModels

end SurfaceRealUpperHalfPlaneBranchAtlasData

end

end JJMath
