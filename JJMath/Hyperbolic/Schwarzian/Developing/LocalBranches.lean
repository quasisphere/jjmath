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

/-- The local projective/developing coordinate obtained by solving the Schwarzian ODE.
%%handwave
name:
  Local coordinate defined by a Schwarzian ODE frame
statement:
  A local Schwarzian ODE chart has developing coordinate $f=y_1/y_0$, the quotient stored by its solution frame.
-/
def localMap {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (C : LocalSchwarzianODEChart S) : ℂ → ℂ :=
  C.frame.localMap

/--
%%handwave
name: Schwarzian equation for a local ODE coordinate
statement:
  Let $f=y_1/y_0$ be the local coordinate obtained from a fundamental solution pair for $y''+\frac12S(z)y=0$. On its domain, $\{f,z\}=S(z)$.
proof:
  This is the Schwarzian identity supplied by the underlying linear ODE frame.
-/
theorem schwarzian_eq_coefficient
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (C : LocalSchwarzianODEChart S) :
    ∀ z, z ∈ C.domain →
      schwarzianExpression C.frame.localMapDeriv C.frame.localMapSecondDeriv
        C.frame.localMapThirdDeriv z = S.coefficient z :=
  C.frame.schwarzianExpression_eq_coefficient

/--
%%handwave
name: Nonvanishing derivative of a local Schwarzian coordinate
statement:
  The local coordinate $f=y_1/y_0$ obtained from a nondegenerate Schwarzian ODE frame satisfies $f'(z)\ne0$ throughout its domain.
proof:
  Apply the nonvanishing-derivative conclusion of the underlying ODE frame.
-/
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

end LocalProjectiveDevelopingMap

/--
Concrete holomorphicity predicate for an upper-half-plane-valued local branch.

We phrase this pointwise as complex differentiability of the complex-valued
coercion on the relevant open domain.  This is the shape most of the local
Schwarzian and pullback API already consumes.

%%handwave
name:
  Holomorphic upper-half-plane-valued map on a domain
statement:
  A map $f:\mathbb C\to\mathbb H$ is holomorphic on $U$ when its complex-valued coercion is complex differentiable at every point of $U$.
-/
def LocalUpperHalfPlaneMapHolomorphicOn (U : Set ℂ) (f : ℂ → ℍ) : Prop :=
  ∀ z, z ∈ U → DifferentiableAt ℂ (fun w : ℂ ↦ (f w : ℂ)) z

namespace LocalUpperHalfPlaneMapHolomorphicOn

/--
%%handwave
name: Holomorphicity from prescribed complex derivatives
statement:
  Let $f:U\to\mathbb H$. If for every $z\in U$ the complex-valued map $f$ has a complex derivative $f'(z)$ at $z$, then $f$ is holomorphic on $U$.
proof:
  Existence of a complex derivative at each point is precisely pointwise complex differentiability on $U$.
-/
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

/-- The domain of a local upper-half-plane developing map.
%%handwave
name:
  Domain of an upper-half-plane developing branch
statement:
  The domain of a local upper-half-plane developing map is the open coordinate domain of its underlying projective branch.
-/
def domain {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) : Set ℂ :=
  H.projective.domain

/--
Two local upper-half-plane developing maps have a real Mobius transition on
their overlap.

This is the local form of the real-holonomy statement: once Schwarzian ODE
solutions have been normalized to recover the same hyperbolic metric as
`ℍ`-valued maps, their coordinate change should be an orientation-preserving
isometry of the upper half-plane, hence an element of `PSL(2, ℝ)`.

%%handwave
name:
  Real Möbius transition between upper-half-plane branches
statement:
  Two branches $F_1,F_2$ have a real Möbius transition when some $A\in\mathrm{PSL}_2(\mathbb R)$ satisfies $F_2(z)=A\cdot F_1(z)$ throughout their common domain.
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

%%handwave
name:
  Pointed real Möbius transition of branch one-jets
statement:
  A transformation $A\in\mathrm{PSL}_2(\mathbb R)$ gives a pointed transition at $z_0$ when both branches are defined there and $F_2(z_0)=A\cdot F_1(z_0)$ together with $F_2'(z_0)=(A\circ F_1)'(z_0)$.
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

/--
%%handwave
name: Positive squared norm of the developing-map derivative
statement:
  If the derivative $F'(z)$ of a local projective developing coordinate is nonzero, then $|F'(z)|^2>0$.
proof:
  The complex squared norm is positive exactly for nonzero complex numbers.
-/
theorem affineDerivativeNormSq_pos
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) {z : ℂ}
    (hz : z ∈ H.domain) :
    0 < Complex.normSq (H.projective.affineMapDeriv z) :=
  Complex.normSq_pos.mpr (H.projective.affineMapDeriv_ne_zero z hz)

/--
%%handwave
name: Positive derivative norm of an upper-half-plane branch
statement:
  The squared norm of the complex derivative of a local upper-half-plane developing map is positive at every point of its domain.
proof:
  Identify the actual derivative with the nonzero derivative stored by the projective developing map, then use positivity of its squared norm.
-/
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

%%handwave
name:
  Squared hyperbolic norm of a branch derivative
statement:
  For $F:\Omega\to\mathbb H$, the squared hyperbolic norm of its derivative at $z$ is $|F'(z)|^2/(\operatorname{Im}F(z))^2$.
-/
def hyperbolicDerivativeNormSqAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (z : ℂ) : ℝ :=
  complexDerivativeNormSq H.upperHalfPlaneMap z / ((H.upperHalfPlaneMap z : ℂ).im ^ 2)

/--
%%handwave
name: Hyperbolic derivative norm of a metric-recovering branch
statement:
  Let $F:\Omega\to\mathbb H$ recover a conformal factor $u$ by the Poincare pullback formula. Then $|F'(z)|^2/(\operatorname{Im}F(z))^2=e^{2u(z)}$ for every $z\in\Omega$.
proof:
  Replace the actual derivative by the derivative stored with the projective branch and apply the metric-recovery identity.
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
%%handwave
name: Equal hyperbolic derivative norms on branch overlaps
statement:
  If $F_1$ and $F_2$ both recover the same conformal factor $u$, then at every point $z$ in both domains,
  $$\frac{|F_1'(z)|^2}{(\operatorname{Im}F_1(z))^2}=\frac{|F_2'(z)|^2}{(\operatorname{Im}F_2(z))^2}.$$
proof:
  Both sides equal the common squared conformal density $e^{2u(z)}$.
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

/--
Turn a coordinate upper-half-plane Schwarzian branch into a local Liouville
developing solution for a surface chart whose coordinate image lies in the
branch domain.

This is the chartwise version of `toLocalLiouvilleDevelopingSolution`: the
surface domain and coordinate come from an existing local Liouville metric
formula, while the conformal factor is restricted to the chosen Schwarzian
branch domain.

%%handwave
name:
  Surface Liouville developing solution from a coordinate branch
statement:
  A metric-recovering branch $F$ whose domain contains the image of a surface Liouville chart determines a local developing solution by using $F$ as the coordinate map and its Poincaré pullback identity as the metric formula.
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

%%handwave
name:
  Metric formula restricted to a selected Schwarzian branch
statement:
  At $x$, restrict the local Liouville metric formula to those surface points whose coordinate lies in the domain of the branch selected at $x$.
-/
def restrictedFormulaAt
    (B : SurfaceSchwarzianPointedBranchPreData A) (x : X) :
    LocalLiouvilleMetricFormula X g :=
  (A.formulaAt x).restrictDomainToCoordinateSubset (B.branchAt x).domain
    (B.branchAt x).projective.domain_subset (B.restricted_domain_open x)

/--
Shrink every metric formula in the atlas to the branch domain chosen at its
base point.

%%handwave
name:
  Metric-formula atlas restricted to selected branches
statement:
  Restrict each formula in a local Liouville atlas to the inverse image of its selected coordinate-branch domain, retaining a formula centered at every surface point.
-/
def toRestrictedMetricFormulaAtlas
    (B : SurfaceSchwarzianPointedBranchPreData A) :
    LocalLiouvilleMetricFormulaAtlas X g where
  formulaAt := B.restrictedFormulaAt
  mem_formulaAt_domain := by
    intro x
    exact ⟨A.mem_formulaAt_domain x, B.center_mem_branch x⟩

/-- The local Liouville developing solution on the restricted formula at `x`.
%%handwave
name:
  Developing solution associated to a selected surface branch
statement:
  The branch selected at $x$, applied to the metric formula restricted to its domain, determines a local Liouville developing solution near $x$.
-/
def solutionAt
    (B : SurfaceSchwarzianPointedBranchPreData A) (x : X) :
    LocalLiouvilleDevelopingSolution X g :=
  (B.branchAt x).toLocalLiouvilleDevelopingSolutionOfMetricFormula
    (F := B.restrictedFormulaAt x) (by
      intro y hy
      exact hy.2)

end SurfaceSchwarzianPointedBranchPreData



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

/-- The branch chosen near a point, with a shorter name.
%%handwave
name:
  Selected upper-half-plane branch near a coordinate point
statement:
  A local branch atlas assigns to each $z$ in the conformal coordinate domain its chosen upper-half-plane developing branch.
-/
def branchNear {u : LocalConformalFactor}
    (A : LocalUpperHalfPlaneBranchAtlas u) (z : u.coordinateDomain) :
    LocalUpperHalfPlaneDevelopingMap (A.schwarzianAt z) :=
  A.branchAt z

/--
%%handwave
name: A chosen local branch contains its center
statement:
  In a local upper-half-plane branch atlas over a coordinate domain $U$, the branch selected near each $z\in U$ is defined at $z$.
proof:
  This is the center-covering property of the branch atlas.
-/
theorem mem_branchNear_domain {u : LocalConformalFactor}
    (A : LocalUpperHalfPlaneBranchAtlas u) (z : u.coordinateDomain) :
    (z : ℂ) ∈ (A.branchNear z).domain :=
  A.mem_branchAt_domain z




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

/-- The base coordinate of the formula centered at `x`.
%%handwave
name:
  Base coordinate of a surface metric formula
statement:
  For the local metric formula centered at $x$, its base coordinate is the point $\phi_x(x)$ in the conformal-factor domain.
-/
def baseCoordinate
    (_B : SurfaceRealUpperHalfPlaneBranchAtlasPreData A) (x : X) :
    (A.formulaAt x).conformalFactor.coordinateDomain :=
  ⟨(A.formulaAt x).coordinate x,
    (A.formulaAt x).coordinate_mem_conformalFactor_domain x
      (A.mem_formulaAt_domain x)⟩

/-- The real coordinate branch atlas chosen at `x`.
%%handwave
name:
  Real branch atlas chosen at a surface point
statement:
  At every surface point $x$, retain the chosen coordinate-domain atlas of metric-recovering branches with real Möbius transitions.
-/
def realBranchAtlas
    (B : SurfaceRealUpperHalfPlaneBranchAtlasPreData A) (x : X) :
    LocalRealUpperHalfPlaneBranchAtlas (A.formulaAt x).conformalFactor :=
  B.realBranchAtlasAt x

/-- The Schwarzian data of the selected branch at `x`.
%%handwave
name:
  Schwarzian coefficient data selected at a surface point
statement:
  At $x$, select the Schwarzian data attached to the coordinate branch centered at $\phi_x(x)$.
-/
def schwarzianAt
    (B : SurfaceRealUpperHalfPlaneBranchAtlasPreData A) (x : X) :
    LocalSchwarzianData (A.formulaAt x).conformalFactor :=
  (B.realBranchAtlas x).schwarzianAt (B.baseCoordinate x)

/-- The selected upper-half-plane branch at `x`.
%%handwave
name:
  Upper-half-plane branch selected at a surface point
statement:
  At $x$, select from the real coordinate branch atlas the upper-half-plane branch centered at the base coordinate $\phi_x(x)$.
-/
def branchAt
    (B : SurfaceRealUpperHalfPlaneBranchAtlasPreData A) (x : X) :
    LocalUpperHalfPlaneDevelopingMap (B.schwarzianAt x) :=
  (B.realBranchAtlas x).branchNear (B.baseCoordinate x)

/--
%%handwave
name: The selected surface branch contains its center
statement:
  Let a real upper-half-plane branch atlas be chosen for the coordinate formula centered at a surface point $x$. The branch selected at the base coordinate $\phi_x(x)$ is defined at that coordinate.
proof:
  Apply the center-covering property of the chosen coordinate branch atlas at the base coordinate.
-/
theorem center_mem_branch
    (B : SurfaceRealUpperHalfPlaneBranchAtlasPreData A) (x : X) :
    (A.formulaAt x).coordinate x ∈ (B.branchAt x).domain :=
  (B.realBranchAtlas x).mem_branchNear_domain (B.baseCoordinate x)

/-- Convert coordinate real branch atlases into pointed surface branch predata.
%%handwave
name:
  Pointed surface branch data from coordinate real branch atlases
statement:
  A real branch atlas in every surface coordinate determines pointed branch data by choosing the branch centered at each base coordinate and recording the openness of its pulled-back domain.
-/
def toSurfaceSchwarzianPointedBranchPreData
    (B : SurfaceRealUpperHalfPlaneBranchAtlasPreData A) :
    SurfaceSchwarzianPointedBranchPreData A where
  schwarzianAt := B.schwarzianAt
  branchAt := B.branchAt
  center_mem_branch := B.center_mem_branch
  restricted_domain_open := B.restricted_domain_open

end SurfaceRealUpperHalfPlaneBranchAtlasPreData



end

end JJMath
