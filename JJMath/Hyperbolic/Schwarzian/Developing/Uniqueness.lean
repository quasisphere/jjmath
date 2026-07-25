import JJMath.Hyperbolic.Schwarzian.Developing.RealMobiusTransitions

/-!
# Split Schwarzian developing-map constructions
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

/--
The one-jet equality locus of a pointed real-Mobius comparison, viewed as a
subset of the common overlap.

This is the right equality locus for local uniqueness: matching only the value
at a point is not enough, while matching value and complex derivative is.

%%handwave
name:
  One-jet equality locus for a real Möbius comparison
statement:
  For branches $F_1,F_2$ and $A\in\mathrm{PSL}_2(\mathbb R)$, the equality locus consists of overlap points $z$ where $F_2(z)=A\cdot F_1(z)$ and $F_2'(z)=(A\circ F_1)'(z)$.
-/
def pointedRealMobiusTransitionOneJetEqualitySet
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) :
    Set {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} :=
  {z | H₂.upperHalfPlaneMap (z : ℂ) =
        realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap (z : ℂ)) ∧
      deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (z : ℂ) =
        deriv
          (fun w : ℂ ↦ (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
          (z : ℂ)}

/--
Continuity target sufficient for closedness of the pointed real-Mobius
equality locus.

%%handwave
name:
  Continuity of a pointed real Möbius comparison
statement:
  This proposition asserts that on the common domain of two metric-recovering branches, both $F_2$ and $A\circ F_1$ are continuous whenever $A$ matches their one-jets at a point.
-/
def PointedRealMobiusTransitionEqualitySetContinuityTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          Continuous
            (fun z : {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} ↦
              H₂.upperHalfPlaneMap (z : ℂ)) ∧
          Continuous
            (fun z : {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} ↦
              realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap (z : ℂ)))

/-- Continuity of an upper-half-plane branch on its own domain.
%%handwave
name:
  Continuity of local upper-half-plane developing branches
statement:
  This proposition asserts that every local developing branch is continuous on its domain as a map into $\mathbb H$.
-/
def LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S),
      Continuous (fun z : {z : ℂ // z ∈ H.domain} ↦ H.upperHalfPlaneMap (z : ℂ))

/-- Continuity of an upper-half-plane branch as a complex-valued map on its domain.
%%handwave
name:
  Complex-valued continuity of local developing branches
statement:
  This proposition asserts that the complex-valued function underlying every local upper-half-plane developing branch is continuous on its domain.
-/
def LocalUpperHalfPlaneDevelopingMapComplexContinuousOnDomainTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S),
      ContinuousOn (fun z : ℂ ↦ (H.upperHalfPlaneMap z : ℂ)) H.domain

/--
Complex-valued continuity of a branch on its domain gives continuity of the
upper-half-plane-valued restricted branch.


%%handwave
name:
  Complex continuity gives upper-half-plane-valued continuity
statement:
  If the complex-valued function underlying an upper-half-plane developing branch F is continuous on its domain, then F is continuous there as a map into the upper half plane.
proof:
  Use continuity into the subtype exactly when the ambient complex-valued map is continuous and already lands in the subtype.
-/
theorem localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem_of_complexContinuousOn
    (hComplex : LocalUpperHalfPlaneDevelopingMapComplexContinuousOnDomainTheorem) :
    LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem := by
  intro u S H
  let f : ℂ → ℂ := fun z ↦ (H.upperHalfPlaneMap z : ℂ)
  have hf : Continuous (H.domain.restrict f) :=
    continuousOn_iff_continuous_restrict.mp (hComplex H)
  exact continuous_induced_rng.mpr (by
    simpa [Function.comp_def, f, Set.restrict] using hf)

/--
The actual nonzero derivative stored by every upper-half-plane developing
branch gives branch-domain continuity.


%%handwave
name:
  Every upper-half-plane developing branch is continuous as a complex-valued map
statement:
  The complex-valued function underlying every local upper-half-plane developing branch is continuous on its domain.
proof:
  The stored nonzero complex derivative makes the branch complex differentiable at every domain point, hence continuous there.
-/
theorem localUpperHalfPlaneDevelopingMapComplexContinuousOnDomainTheorem :
    LocalUpperHalfPlaneDevelopingMapComplexContinuousOnDomainTheorem := by
  intro u S H z hz
  let f : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  have hf_ne : deriv f z ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, f] at hpos
    exact Complex.normSq_pos.mp hpos
  exact ((differentiableAt_of_deriv_ne_zero hf_ne).hasDerivAt).continuousAt.continuousWithinAt

/-- Upper-half-plane developing branches are continuous on their domains.

%%handwave
name:
  Every upper-half-plane developing branch is continuous
statement:
  Every local upper-half-plane developing branch is continuous on its domain as a map into the upper half plane.
proof:
  First prove continuity of the underlying complex-valued map from its derivative, then transfer continuity to the upper-half-plane subtype.
-/
theorem localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem :
    LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem :=
  localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem_of_complexContinuousOn
    localUpperHalfPlaneDevelopingMapComplexContinuousOnDomainTheorem

/-- Continuity of every fixed real-Mobius action on the upper half-plane.
%%handwave
name:
  Continuity of real Möbius transformations on $\mathbb H$
statement:
  This proposition asserts that for every $A\in\mathrm{PSL}_2(\mathbb R)$, the map $z\mapsto A\cdot z$ is continuous on $\mathbb H$.
-/
def RealMobiusRepresentativeActionContinuousTheorem : Prop :=
  ∀ A : RealMobiusRepresentative, Continuous (realMobiusRepresentativeAction A)

/-- Fixed real-Mobius actions are continuous on the upper half-plane.

%%handwave
name:
  Real Möbius transformations act continuously on the upper half plane
statement:
  For every real Möbius transformation A, the map z ↦ A(z) is continuous on the upper half plane.
proof:
  The denominator of a real Möbius transformation is nonzero on the upper half plane, so continuity follows from the quotient formula.
-/
theorem realMobiusRepresentativeActionContinuousTheorem :
    RealMobiusRepresentativeActionContinuousTheorem :=
  realMobiusRepresentativeAction_continuous

/--
Domain continuity of branches and continuity of real-Mobius actions imply the
overlap-continuity target for the equality locus.


%%handwave
name:
  Branch continuity makes a Möbius comparison continuous
statement:
  Let F₁ and F₂ be upper-half-plane developing branches and A a real Möbius transformation. If the branches and the action of A are continuous, then F₂ and A ∘ F₁ are continuous on their common domain.
proof:
  Restrict F₂ to the overlap and compose the restriction of F₁ with the continuous action of A.
-/
theorem pointedRealMobiusTransitionEqualitySetContinuityTheorem_of_branch_and_action_continuity
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAction : RealMobiusRepresentativeActionContinuousTheorem) :
    PointedRealMobiusTransitionEqualitySetContinuityTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ _hu _hpoint
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  let toH₁Domain : overlap → {z : ℂ // z ∈ H₁.domain} :=
    fun z ↦ ⟨(z : ℂ), z.property.1⟩
  let toH₂Domain : overlap → {z : ℂ // z ∈ H₂.domain} :=
    fun z ↦ ⟨(z : ℂ), z.property.2⟩
  have htoH₁ : Continuous toH₁Domain := by
    exact continuous_subtype_val.subtype_mk (fun z ↦ z.property.1)
  have htoH₂ : Continuous toH₂Domain := by
    exact continuous_subtype_val.subtype_mk (fun z ↦ z.property.2)
  have h₂ :
      Continuous
        (fun z : overlap ↦ H₂.upperHalfPlaneMap (z : ℂ)) := by
    simpa [toH₂Domain] using (hBranch H₂).comp htoH₂
  have h₁ :
      Continuous
        (fun z : overlap ↦ H₁.upperHalfPlaneMap (z : ℂ)) := by
    simpa [toH₁Domain] using (hBranch H₁).comp htoH₁
  exact ⟨h₂, (hAction A).comp h₁⟩

/--
Metric-Schwarzian identifications for two branches over the same conformal
factor imply coefficient agreement on their overlap.


%%handwave
name:
  Branches recovering the same metric have equal Schwarzian coefficients
statement:
  Let F₁ and F₂ be local developing branches for the same conformal factor u. If each stored Schwarzian coefficient is identified with 2(u_{zz} − u_z²), then their coefficients agree at every point of the common domain.
proof:
  Both coefficients equal the same metric Schwarzian expression pointwise.
-/
theorem sameSchwarzianCoefficientOnOverlap_of_originalMetricIdentifications
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hS₁ : LocalOriginalMetricSchwarzianIdentification S₁)
    (hS₂ : LocalOriginalMetricSchwarzianIdentification S₂) :
    ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
      S₁.coefficient z = S₂.coefficient z := by
  intro z hz₁ _hz₂
  have hzcoord : z ∈ u.coordinateDomain :=
    H₁.projective.domain_subset hz₁
  rw [hS₁.coefficient_eq_metric z hzcoord, hS₂.coefficient_eq_metric z hzcoord]

/--
The first-Wirtinger expression attached to an upper-half-plane branch.

For a branch `F : U → ℍ` pulling back the Poincare metric to `e^{2u}|dz|²`,
this is the expected value of `u_z`.

%%handwave
name:
  First Wirtinger expression of a metric-recovering branch
statement:
  For a branch $F:\Omega\to\mathbb H$, define the branch expression for $u_z$ by $\tfrac12\left(F''/F'+iF'/\operatorname{Im}F\right)$.
-/
def localUpperHalfPlaneDevelopingMapFirstWirtingerExpression
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (z : ℂ) : ℂ :=
  (deriv (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z /
    deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z +
    Complex.I * deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z /
      (((H.upperHalfPlaneMap z : ℂ).im : ℝ) : ℂ)) / 2

/--
The Schwarzian expression built from Lean's actual iterated complex
derivatives of a scalar map.

%%handwave
name:
  Actual Schwarzian derivative of a scalar map
statement:
  For a scalar map $f$, its actual Schwarzian is $S(f)=f'''/f'-\tfrac32(f''/f')^2$, using iterated complex derivatives.
-/
def actualSchwarzian (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  schwarzianExpression
    (fun w : ℂ ↦ deriv f w)
    (fun w : ℂ ↦ deriv (fun t : ℂ ↦ deriv f t) w)
    (fun w : ℂ ↦
      deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) w)
    z

/--
The first-Wirtinger expression after postcomposing an upper-half-plane branch
by a real Mobius transformation.

%%handwave
name:
  First Wirtinger expression after real Möbius postcomposition
statement:
  For $A\in\mathrm{PSL}_2(\mathbb R)$ and a branch $F$, this is $\tfrac12\left((A\circ F)''/(A\circ F)'+i(A\circ F)'/\operatorname{Im}(A\circ F)\right)$.
-/
def realMobiusPostcompositionFirstWirtingerExpression
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S)
    (A : RealMobiusRepresentative) (z : ℂ) : ℂ :=
  (deriv
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
          w) z /
    deriv
      (fun w : ℂ ↦
        (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ)) z +
    Complex.I *
      deriv
        (fun w : ℂ ↦
          (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ)) z /
      ((((realMobiusRepresentativeAction A (H.upperHalfPlaneMap z) : ℍ) : ℂ).im : ℝ) :
        ℂ)) / 2

/--
Fixed-branch projective-symbolic derivative regularity.

This is the local version of the two global projective derivative interfaces:
it is the exact information produced for each branch in the strengthened
Frobenius normalization atlas.
-/
structure LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) : Prop where
  /-- The stored affine derivative has the stored second derivative. -/
  projectiveFirstDerivative_hasDerivAt :
    ∀ {z : ℂ}, z ∈ H.domain →
      HasDerivAt
        (fun w : ℂ ↦ H.projective.affineMapDeriv w)
        (H.projective.affineMapSecondDeriv z)
        z
  /-- The stored second derivative has the stored third derivative. -/
  projectiveSecondDerivative_hasDerivAt :
    ∀ {z : ℂ}, z ∈ H.domain →
      HasDerivAt
        (fun w : ℂ ↦ H.projective.affineMapSecondDeriv w)
        (H.projective.affineMapThirdDeriv z)
        z

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/-- Fixed-branch projective first-derivative regularity gives actual first-derivative regularity.

%%handwave
name:
  Projective regularity identifies the derivative of the branch derivative
statement:
  If an upper-half-plane branch F has stored projective derivatives through third order, then at every domain point the actual derivative F′ has derivative equal to the stored second derivative F₂.
proof:
  Identify F′ with the stored first derivative locally and use the stored identity F₁′ = F₂.
-/
theorem firstDerivative_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    {z : ℂ} (hz : z ∈ H.domain) :
    HasDerivAt
      (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w)
      (H.projective.affineMapSecondDeriv z)
      z := by
  have hEq :
      (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w)
        =ᶠ[nhds z]
      (fun w : ℂ ↦ H.projective.affineMapDeriv w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa using H.upperHalfPlane_deriv_eq_projectiveDeriv w hw
  exact (R.projectiveFirstDerivative_hasDerivAt hz).congr_of_eventuallyEq hEq

/--
Fixed-branch projective derivative regularity gives actual second-derivative
regularity.


%%handwave
name:
  Projective regularity identifies the third derivative of a branch
statement:
  If an upper-half-plane branch F has stored projective derivatives through third order, then at every domain point the actual second derivative has derivative equal to the stored third derivative F₃.
proof:
  Identify the actual first and second derivatives with the stored branches and use F₂′ = F₃.
-/
theorem secondDerivative_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    {z : ℂ} (hz : z ∈ H.domain) :
    HasDerivAt
      (fun w : ℂ ↦
        deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ (H.upperHalfPlaneMap s : ℂ)) t) w)
      (H.projective.affineMapThirdDeriv z)
      z := by
  have hEq :
      (fun w : ℂ ↦
        deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ (H.upperHalfPlaneMap s : ℂ)) t) w)
        =ᶠ[nhds z]
      (fun w : ℂ ↦ H.projective.affineMapSecondDeriv w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    exact (R.firstDerivative_hasDerivAt hw).deriv
  exact (R.projectiveSecondDerivative_hasDerivAt hz).congr_of_eventuallyEq hEq

/--
Fixed-branch projective derivative regularity gives the differentiability
interface for the actual derivative branch.


%%handwave
name:
  Projective regularity makes the actual derivative differentiable
statement:
  Under projective derivative regularity, the actual derivative F′ of an upper-half-plane branch is complex differentiable at every point of its domain, with derivative F″.
proof:
  Use the pointwise derivative identity for F′ and rewrite its value as the actual second derivative.
-/
theorem derivative_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    {z : ℂ} (hz : z ∈ H.domain) :
    HasDerivAt
      (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w)
      (deriv (fun w : ℂ ↦
        deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z)
      z := by
  have h := R.firstDerivative_hasDerivAt hz
  convert h using 1
  exact h.deriv

/-- Fixed-branch derivative regularity gives continuity of the stored affine derivative.

%%handwave
name:
  Projective regularity makes the affine derivative continuous
statement:
  If the stored affine derivative F₁ of a developing branch satisfies F₁′ = F₂ throughout the domain, then F₁ is continuous there.
proof:
  Pointwise complex differentiability implies continuity on the domain.
-/
theorem affineDerivative_continuousOn
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H) :
    ContinuousOn (fun z : ℂ ↦ H.projective.affineMapDeriv z) H.domain := by
  have hActual :
      ContinuousOn
        (fun z : ℂ ↦ deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z)
        H.domain := by
    intro z hz
    exact (R.firstDerivative_hasDerivAt hz).continuousAt.continuousWithinAt
  exact hActual.congr (fun z hz ↦ by
    exact (H.upperHalfPlane_deriv_eq_projectiveDeriv z hz).symm)

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Coefficient-aware local uniqueness with only fixed-pair projective derivative
regularity.

This is the final local identity-principle shape needed by the derivative-data
normalization atlas: the two compared branches carry their own derivative
regularity data, rather than relying on a global theorem for every possible
upper-half-plane branch.

%%handwave
name:
  One-jet local uniqueness with coefficient and derivative agreement
statement:
  This proposition asserts that two regular upper-half-plane branches with equal Schwarzian coefficient, whose values and first derivatives match after a fixed real Möbius map at a point, continue to have matching one-jets on some neighborhood.
-/
def PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁ →
        LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂ →
          u.SolvesLiouvilleEquation →
            H₁.HasPointedRealMobiusTransition H₂ A z₀ →
              (∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
                S₁.coefficient z = S₂.coefficient z) →
              ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
                H₂.upperHalfPlaneMap z =
                    realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) →
                deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z =
                    deriv
                      (fun w : ℂ ↦
                        (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
                      z →
                  ∃ U : Set ℂ,
                    IsOpen U ∧ z ∈ U ∧ U ⊆ H₁.domain ∩ H₂.domain ∧
                      ∀ w, w ∈ U →
                        H₂.upperHalfPlaneMap w =
                            realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) ∧
                        deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w =
                            deriv
                              (fun t : ℂ ↦
                                (realMobiusRepresentativeAction A
                                  (H₁.upperHalfPlaneMap t) : ℂ))
                              w

/--
Fixed-pair projective derivative regularity makes the one-jet equality locus
closed on the overlap.


%%handwave
name:
  Projective derivative regularity closes the Möbius one-jet equality locus
statement:
  Let F₁ and F₂ be upper-half-plane branches with projective derivative regularity, and let A be a real Möbius transformation. Then the locus where F₂ = A ∘ F₁ and F₂′ = (A ∘ F₁)′ is closed in their common domain.
proof:
  Projective regularity gives continuity of both branches and their affine derivatives; apply the closed one-jet equalizer theorem.
-/
theorem pointedRealMobiusTransitionOneJetEqualitySet_isClosed_of_pairProjectiveDerivative
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (hu : u.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂) :
    IsClosed (pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A) := by
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  have hValue :
      Continuous
        (fun z : overlap ↦ H₂.upperHalfPlaneMap (z : ℂ)) ∧
      Continuous
        (fun z : overlap ↦
          realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap (z : ℂ))) :=
    pointedRealMobiusTransitionEqualitySetContinuityTheorem_of_branch_and_action_continuity
      localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem
      realMobiusRepresentativeActionContinuousTheorem
      H₁ H₂ A z₀ hu hpoint
  rcases hValue with ⟨h₂, hA⟩
  have hH₂DerivOnOverlap :
      ContinuousOn
        (fun z : ℂ ↦ deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z)
        overlap := by
    have hOn :
        ContinuousOn
          (fun z : ℂ ↦ deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z)
          H₂.domain :=
      R₂.affineDerivative_continuousOn.congr (fun z hz ↦ by
        exact H₂.upperHalfPlane_deriv_eq_projectiveDeriv z hz)
    exact hOn.mono (fun z hz ↦ hz.2)
  have hd₂ :
      Continuous
        (fun z : overlap ↦
          deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (z : ℂ)) := by
    simpa [Set.restrict] using
      (continuousOn_iff_continuous_restrict.mp hH₂DerivOnOverlap)
  let toH₁Domain : overlap → {z : ℂ // z ∈ H₁.domain} :=
    fun z ↦ ⟨(z : ℂ), z.property.1⟩
  have htoH₁ : Continuous toH₁Domain := by
    exact continuous_subtype_val.subtype_mk (fun z ↦ z.property.1)
  have hH₁ :
      Continuous (fun z : overlap ↦ H₁.upperHalfPlaneMap (z : ℂ)) := by
    simpa [toH₁Domain] using
      (localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem H₁).comp htoH₁
  have hfactor :
      Continuous
        (fun z : overlap ↦
          deriv
            (fun w : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
            (H₁.upperHalfPlaneMap (z : ℂ))) :=
    (realMobiusRepresentativeAction_deriv_continuous A).comp hH₁
  have hH₁DerivOnOverlap :
      ContinuousOn
        (fun z : ℂ ↦ deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ)) z)
        overlap := by
    have hOn :
        ContinuousOn
          (fun z : ℂ ↦ deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ)) z)
          H₁.domain :=
      R₁.affineDerivative_continuousOn.congr (fun z hz ↦ by
        exact H₁.upperHalfPlane_deriv_eq_projectiveDeriv z hz)
    exact hOn.mono (fun z hz ↦ hz.1)
  have hbranchDeriv :
      Continuous
        (fun z : overlap ↦
          deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ)) (z : ℂ)) := by
    simpa [Set.restrict] using
      (continuousOn_iff_continuous_restrict.mp hH₁DerivOnOverlap)
  have hprod :
      Continuous
        (fun z : overlap ↦
          deriv
            (fun w : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
            (H₁.upperHalfPlaneMap (z : ℂ)) *
          deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ)) (z : ℂ)) :=
    hfactor.mul hbranchDeriv
  have htarget_eq :
      (fun z : overlap ↦
        deriv
          (fun w : ℂ ↦
            (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
          (z : ℂ))
      =
      (fun z : overlap ↦
        deriv
          (fun w : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
          (H₁.upperHalfPlaneMap (z : ℂ)) *
        deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ)) (z : ℂ)) := by
    funext z
    exact realMobiusBranchPostcompositionDerivativeChainRuleTheorem H₁ A z.property.1
  have hdA :
      Continuous
        (fun z : overlap ↦
          deriv
            (fun w : ℂ ↦
              (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
            (z : ℂ)) := by
    rw [htarget_eq]
    exact hprod
  have hValueClosed :
      IsClosed
        {z : overlap |
          H₂.upperHalfPlaneMap (z : ℂ) =
            realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap (z : ℂ))} :=
    isClosed_eq h₂ hA
  have hDerivClosed :
      IsClosed
        {z : overlap |
          deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (z : ℂ) =
            deriv
              (fun w : ℂ ↦
                (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
              (z : ℂ)} :=
    isClosed_eq hd₂ hdA
  simpa [pointedRealMobiusTransitionOneJetEqualitySet, Set.setOf_and] using
    hValueClosed.inter hDerivClosed

/--
For one fixed pair of branches, coefficient agreement and the pair-shaped
local uniqueness theorem make the one-jet equality locus open.


%%handwave
name:
  Coefficient agreement and local uniqueness open the one-jet equality locus
statement:
  Let F₁ and F₂ be projectively regular developing branches with equal Schwarzian coefficients on their overlap. If equal one-jets imply local equality for such a pair, then the locus where F₂ and A ∘ F₁ have equal one-jets is open in the overlap.
proof:
  At each point of the equality locus, apply the pairwise Schwarzian uniqueness hypothesis to obtain an open neighborhood contained in the locus.
-/
theorem pointedRealMobiusTransitionOneJetEqualitySet_isOpen_of_pairProjectiveDerivative_coefficientAgreement
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (hu : u.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem) :
    IsOpen (pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A) := by
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  let E : Set overlap := pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A
  rw [isOpen_iff_forall_mem_open]
  intro z hzE
  rcases hUnique H₁ H₂ A z₀ R₁ R₂ hu hpoint hCoeff (z : ℂ)
      z.property.1 z.property.2 hzE.1 hzE.2 with
    ⟨U, hUopen, hzU, hUsubset, hUeq⟩
  refine ⟨Subtype.val ⁻¹' U, ?_, hUopen.preimage continuous_subtype_val, hzU⟩
  intro y hy
  exact hUeq (y : ℂ) hy

/--
%%handwave
name:
  Extension of a real Möbius comparison across an overlap
statement:
  Let $F_1,F_2$ be regular local maps to $\mathbb H$ on domains whose
  intersection $W$ is preconnected. Suppose their Schwarzian coefficients
  agree on $W$, and that for some $A\in\mathrm{PSL}_2(\mathbb R)$ the maps
  $F_2$ and $A\circ F_1$ have the same value and first derivative at
  $z_0\in W$. If equality of these one-jets propagates locally, then
  $$F_2=A\circ F_1$$
  throughout $W$, with equality of first derivatives as well.
proof:
  The locus in $W$ where both the values and first derivatives agree is
  nonempty. Derivative regularity makes it closed, while the local
  Schwarzian identity principle makes it open. Preconnectedness therefore
  forces this locus to be all of $W$.
-/
theorem pointedRealMobiusTransition_oneJetExtendsOnPreconnectedOverlap_of_pairProjectiveDerivative_coefficientAgreement
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem)
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : u.SolvesLiouvilleEquation)
    (hconn : IsPreconnected (H₁.domain ∩ H₂.domain))
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z) :
    ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
      H₂.upperHalfPlaneMap z =
          realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) ∧
        deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z =
          deriv
            (fun w : ℂ ↦
              (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
            z := by
  intro z hz₁ hz₂
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  let E : Set overlap := pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A
  haveI : PreconnectedSpace overlap := Subtype.preconnectedSpace hconn
  have hClosed : IsClosed E :=
    pointedRealMobiusTransitionOneJetEqualitySet_isClosed_of_pairProjectiveDerivative
      H₁ H₂ A z₀ hu hpoint R₁ R₂
  have hOpen : IsOpen E :=
    pointedRealMobiusTransitionOneJetEqualitySet_isOpen_of_pairProjectiveDerivative_coefficientAgreement
      H₁ H₂ A z₀ hu hpoint R₁ R₂ hCoeff hUnique
  have hE : IsClopen E := ⟨hClosed, hOpen⟩
  have hbase_mem_overlap : z₀ ∈ overlap := ⟨hpoint.1, hpoint.2.1⟩
  have hbase_mem_E : (⟨z₀, hbase_mem_overlap⟩ : overlap) ∈ E := by
    simpa [E, pointedRealMobiusTransitionOneJetEqualitySet] using hpoint.2.2
  have hE_univ : E = Set.univ :=
    IsClopen.eq_univ hE ⟨⟨z₀, hbase_mem_overlap⟩, hbase_mem_E⟩
  have hz_mem_overlap : z ∈ overlap := ⟨hz₁, hz₂⟩
  have hz_mem_E : (⟨z, hz_mem_overlap⟩ : overlap) ∈ E := by
    rw [hE_univ]
    exact Set.mem_univ _
  simpa [E, pointedRealMobiusTransitionOneJetEqualitySet] using hz_mem_E

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Fixed-branch projective derivative regularity gives the second-order chain
rule for postcomposition by a real Mobius transformation.


%%handwave
name:
  Projective branch regularity gives the second-order Möbius chain rule
statement:
  For a projectively regular upper-half-plane branch F and real Möbius transformation M, one has (M ∘ F)″ = M″(F)(F′)² + M′(F)F″ at every point of the branch domain.
proof:
  Projective regularity makes F′ differentiable, so the ordinary second-order chain rule applies.
-/
theorem realMobiusPostcompositionSecondDerivativeChainRule
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    deriv
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
          w) z =
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
            w)
        (H.upperHalfPlaneMap z) *
        deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z ^ 2 +
      deriv
        (fun w : ℂ ↦
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
        (H.upperHalfPlaneMap z) *
      deriv (fun w : ℂ ↦
          deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z := by
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let M' : ℂ → ℂ := fun w ↦ deriv M w
  let F' : ℂ → ℂ := fun w ↦ deriv F w
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv F' z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv M' (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hF : HasDerivAt F F₁ z :=
    (differentiableAt_of_deriv_ne_zero hF₁_ne).hasDerivAt
  have hM' : HasDerivAt M' β (F z) := by
    have h :=
      realMobiusRepresentativeAction_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hβ := realMobiusRepresentativeAction_second_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', F, β] using hβ.symm)
  have hM'comp : HasDerivAt (fun w ↦ M' (F w)) (β * F₁) z :=
    hM'.comp z hF
  have hF' : HasDerivAt F' F₂ z := by
    simpa [F', F₂, F] using R.derivative_hasDerivAt hz
  have hprod :
      HasDerivAt (fun w ↦ M' (F w) * F' w)
        (β * F₁ ^ 2 + α * F₂) z := by
    have h := hM'comp.mul hF'
    convert h using 1
    simp [F₁, F₂, α, F', M']
    ring
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
          w) =ᶠ[nhds z]
        (fun w : ℂ ↦ M' (F w) * F' w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa [F, F', M, M'] using
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H A hw
  calc
    deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
            w) z =
        deriv (fun w : ℂ ↦ M' (F w) * F' w) z := hEq.deriv_eq
    _ = β * F₁ ^ 2 + α * F₂ := hprod.deriv

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Fixed-branch projective derivative regularity gives the third-order chain rule
for postcomposition by a real Mobius transformation.


%%handwave
name:
  Projective branch regularity gives the third-order Möbius chain rule
statement:
  For a projectively regular upper-half-plane branch F and real Möbius transformation M, one has (M ∘ F)‴ = M‴(F)(F′)³ + 3M″(F)F′F″ + M′(F)F‴ throughout the branch domain.
proof:
  Projective regularity supplies differentiability through F″; apply the third-order chain rule.
-/
theorem realMobiusPostcompositionThirdDerivativeChainRule
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    deriv
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun s : ℂ ↦
                (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
              t)
          w) z =
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              deriv
                (fun s : ℂ ↦
                  (realMobiusRepresentativeAction A
                    ((UpperHalfPlane.ofComplex : ℂ → ℍ) s) : ℂ))
                t)
            w)
        (H.upperHalfPlaneMap z) *
          deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z ^ 3 +
      3 *
        deriv
          (fun w : ℂ ↦
            deriv
              (fun t : ℂ ↦
                (realMobiusRepresentativeAction A
                  ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
              w)
          (H.upperHalfPlaneMap z) *
          deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z *
          deriv
            (fun w : ℂ ↦
              deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z +
      deriv
        (fun w : ℂ ↦
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
        (H.upperHalfPlaneMap z) *
        deriv
          (fun w : ℂ ↦
            deriv
              (fun t : ℂ ↦
                deriv (fun s : ℂ ↦ (H.upperHalfPlaneMap s : ℂ)) t)
              w) z := by
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let G : ℂ → ℂ :=
    fun w ↦ (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ)
  let M' : ℂ → ℂ := fun w ↦ deriv M w
  let M'' : ℂ → ℂ := fun w ↦ deriv M' w
  let F' : ℂ → ℂ := fun w ↦ deriv F w
  let F'' : ℂ → ℂ := fun w ↦ deriv F' w
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv F' z
  let F₃ : ℂ := deriv F'' z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv M' (F z)
  let γ : ℂ := deriv M'' (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hF : HasDerivAt F F₁ z :=
    (differentiableAt_of_deriv_ne_zero hF₁_ne).hasDerivAt
  have hF' : HasDerivAt F' F₂ z := by
    simpa [F', F₂, F] using R.derivative_hasDerivAt hz
  have hF'' : HasDerivAt F'' F₃ z := by
    have h := R.secondDerivative_hasDerivAt hz
    convert h using 1
    exact h.deriv
  have hM' : HasDerivAt M' β (F z) := by
    have h :=
      realMobiusRepresentativeAction_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hβ := realMobiusRepresentativeAction_second_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', F, β] using hβ.symm)
  have hM'' : HasDerivAt M'' γ (F z) := by
    have h :=
      realMobiusRepresentativeAction_second_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hγ := realMobiusRepresentativeAction_third_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', M'', F, γ] using hγ.symm)
  have hterm₁ :
      HasDerivAt (fun w ↦ M'' (F w) * F' w ^ 2)
        (γ * F₁ ^ 3 + 2 * β * F₁ * F₂) z := by
    have hM''comp : HasDerivAt (fun w ↦ M'' (F w)) (γ * F₁) z :=
      hM''.comp z hF
    have hF'sq : HasDerivAt (fun w ↦ F' w ^ 2) (2 * F₁ * F₂) z := by
      simpa [F₁, F₂, pow_one, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm]
        using hF'.pow 2
    have h := hM''comp.mul hF'sq
    convert h using 1
    ring
  have hterm₂ :
      HasDerivAt (fun w ↦ M' (F w) * F'' w)
        (β * F₁ * F₂ + α * F₃) z := by
    have hM'comp : HasDerivAt (fun w ↦ M' (F w)) (β * F₁) z :=
      hM'.comp z hF
    have h := hM'comp.mul hF''
    convert h using 1
  have hsum :
      HasDerivAt
        (fun w ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w)
        (γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃) z := by
    have h := hterm₁.add hterm₂
    convert h using 1
    ring
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun s : ℂ ↦
                (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
              t)
          w) =ᶠ[nhds z]
        (fun w : ℂ ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa [G, M, M', M'', F, F', F''] using
      R.realMobiusPostcompositionSecondDerivativeChainRule A hw
  calc
    deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              deriv
                (fun s : ℂ ↦
                  (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
                t)
            w)
        z =
        deriv (fun w : ℂ ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w) z :=
      hEq.deriv_eq
    _ = γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃ := hsum.deriv

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Fixed-branch projective derivative regularity gives first-derivative
regularity for a real-Mobius postcomposition.


%%handwave
name:
  Projective regularity makes the first derivative of a Möbius postcomposition differentiable
statement:
  For a projectively regular upper-half-plane branch F and real Möbius map M, the derivative (M ∘ F)′ is complex differentiable at every point of the branch domain.
proof:
  Projective regularity supplies F′′; differentiate M′(F)F′ and identify the result with the actual second derivative.
-/
theorem realMobiusPostcomposition_firstDerivativeHasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    HasDerivAt
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
          w)
      (deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
            w)
        z)
      z := by
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let M' : ℂ → ℂ := fun w ↦ deriv M w
  let F' : ℂ → ℂ := fun w ↦ deriv F w
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv F' z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv M' (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hF : HasDerivAt F F₁ z :=
    (differentiableAt_of_deriv_ne_zero hF₁_ne).hasDerivAt
  have hM' : HasDerivAt M' β (F z) := by
    have h :=
      realMobiusRepresentativeAction_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hβ := realMobiusRepresentativeAction_second_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', F, β] using hβ.symm)
  have hM'comp : HasDerivAt (fun w ↦ M' (F w)) (β * F₁) z :=
    hM'.comp z hF
  have hF' : HasDerivAt F' F₂ z := by
    simpa [F', F₂, F] using R.derivative_hasDerivAt hz
  have hprod :
      HasDerivAt (fun w ↦ M' (F w) * F' w)
        (β * F₁ ^ 2 + α * F₂) z := by
    have h := hM'comp.mul hF'
    convert h using 1
    ring
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
          w) =ᶠ[nhds z]
        (fun w : ℂ ↦ M' (F w) * F' w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa [F, F', M, M'] using
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H A hw
  have hactual :
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
            w)
        z =
        β * F₁ ^ 2 + α * F₂ := by
    simpa [β, α, F₁, F₂, F, M, M'] using
      R.realMobiusPostcompositionSecondDerivativeChainRule A hz
  exact (hprod.congr_of_eventuallyEq hEq).congr_deriv hactual.symm

/--
Fixed-branch projective derivative regularity gives second-derivative
regularity for a real-Mobius postcomposition.


%%handwave
name:
  Projective regularity makes the second derivative of a Möbius postcomposition differentiable
statement:
  For a projectively regular upper-half-plane branch F and real Möbius map M, the second derivative (M ∘ F)″ is complex differentiable at every point of the branch domain.
proof:
  Projective regularity supplies derivatives through F‴; differentiate the second-order chain-rule expression and identify the result with the actual third derivative.
-/
theorem realMobiusPostcomposition_secondDerivativeHasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    HasDerivAt
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun s : ℂ ↦
                (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
              t)
          w)
      (deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              deriv
                (fun s : ℂ ↦
                  (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
                t)
            w)
        z)
      z := by
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let M' : ℂ → ℂ := fun w ↦ deriv M w
  let M'' : ℂ → ℂ := fun w ↦ deriv M' w
  let F' : ℂ → ℂ := fun w ↦ deriv F w
  let F'' : ℂ → ℂ := fun w ↦ deriv F' w
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv F' z
  let F₃ : ℂ := deriv F'' z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv M' (F z)
  let γ : ℂ := deriv M'' (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hF : HasDerivAt F F₁ z :=
    (differentiableAt_of_deriv_ne_zero hF₁_ne).hasDerivAt
  have hF' : HasDerivAt F' F₂ z := by
    simpa [F', F₂, F] using R.derivative_hasDerivAt hz
  have hF'' : HasDerivAt F'' F₃ z := by
    have h := R.secondDerivative_hasDerivAt hz
    convert h using 1
    exact h.deriv
  have hM' : HasDerivAt M' β (F z) := by
    have h :=
      realMobiusRepresentativeAction_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hβ := realMobiusRepresentativeAction_second_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', F, β] using hβ.symm)
  have hM'' : HasDerivAt M'' γ (F z) := by
    have h :=
      realMobiusRepresentativeAction_second_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hγ := realMobiusRepresentativeAction_third_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', M'', F, γ] using hγ.symm)
  have hterm₁ :
      HasDerivAt (fun w ↦ M'' (F w) * F' w ^ 2)
        (γ * F₁ ^ 3 + 2 * β * F₁ * F₂) z := by
    have hM''comp : HasDerivAt (fun w ↦ M'' (F w)) (γ * F₁) z :=
      hM''.comp z hF
    have hF'sq : HasDerivAt (fun w ↦ F' w ^ 2) (2 * F₁ * F₂) z := by
      simpa [F₁, F₂, pow_one, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm]
        using hF'.pow 2
    have h := hM''comp.mul hF'sq
    convert h using 1
    ring
  have hterm₂ :
      HasDerivAt (fun w ↦ M' (F w) * F'' w)
        (β * F₁ * F₂ + α * F₃) z := by
    have hM'comp : HasDerivAt (fun w ↦ M' (F w)) (β * F₁) z :=
      hM'.comp z hF
    have h := hM'comp.mul hF''
    convert h using 1
  have hsum :
      HasDerivAt
        (fun w ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w)
        (γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃) z := by
    have h := hterm₁.add hterm₂
    convert h using 1
    ring
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun s : ℂ ↦
                (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
              t)
          w) =ᶠ[nhds z]
        (fun w : ℂ ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa [M, M', M'', F, F', F''] using
      R.realMobiusPostcompositionSecondDerivativeChainRule A hw
  have hactual :
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              deriv
                (fun s : ℂ ↦
                  (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
                t)
            w)
        z =
        γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃ := by
    simpa [M, M', M'', F, F', F'', γ, β, α, F₁, F₂, F₃] using
      R.realMobiusPostcompositionThirdDerivativeChainRule A hz
  exact (hsum.congr_of_eventuallyEq hEq).congr_deriv hactual.symm

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
The one-variable identity saying that the Poincare first-Wirtinger expression
is invariant under a fixed real Mobius map.

%%handwave
name:
  Real Möbius invariance of the first Wirtinger multiplier
statement:
  This proposition asserts that if $m\in\mathrm{PSL}_2(\mathbb R)$, then $m''(p)/m'(p)+im'(p)/\operatorname{Im}m(p)=i/\operatorname{Im}p$ for every $p\in\mathbb H$.
-/
def RealMobiusFirstWirtingerMultiplierIdentityTheorem : Prop :=
  ∀ (A : RealMobiusRepresentative) (p : ℍ),
    let α : ℂ :=
      deriv
        (fun w : ℂ ↦
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
        p
    let β : ℂ :=
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
            w)
        p
    β / α + Complex.I * α /
      ((((realMobiusRepresentativeAction A p : ℍ) : ℂ).im : ℝ) : ℂ) =
        Complex.I / ((((p : ℍ) : ℂ).im : ℝ) : ℂ)

/--
Pure denominator algebra form of the real-Mobius first-Wirtinger multiplier
identity.

The analytic inputs `m'(z) = (cz+d)^{-2}`, `m''(z) = -2c(cz+d)^{-3}`, and
`Im(mz) = Im(z)/|cz+d|²` are proved separately; this target is only the final
complex-number simplification.

%%handwave
name:
  Denominator algebra for the real Möbius Wirtinger identity
statement:
  This proposition is the algebraic identity obtained by substituting $m'=\delta^{-2}$, $m''=-2c\delta^{-3}$, and $\operatorname{Im}m(p)=\operatorname{Im}p/|\delta|^2$ into the first-Wirtinger multiplier formula.
-/
def RealMobiusFirstWirtingerDenominatorAlgebraTheorem : Prop :=
  ∀ (A : RealMobiusRepresentative) (p : ℍ),
    let δ : ℂ := UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p
    let c : ℂ := ((A : GL (Fin 2) ℝ) 1 0 : ℂ)
    let y : ℂ := ((((p : ℍ) : ℂ).im : ℝ) : ℂ)
    (-2 * c / δ ^ 3) / (δ ^ 2)⁻¹ +
        Complex.I * (δ ^ 2)⁻¹ / (y / (Complex.normSq δ : ℂ)) =
      Complex.I / y

/--
The real and imaginary parts of a Möbius denominator satisfy the required rational identity.

%%handwave
name:
  The real-imaginary Möbius denominator identity
statement:
  For real a,c,y with y ≠ 0 and δ = a+icy ≠ 0, one has (−2c/δ³)/(δ⁻²) + iδ⁻²/(y/|δ|²) = i/y.
proof:
  Clear the nonzero denominators, use |δ|²=a²+c²y² and i²=−1, and simplify the resulting polynomial identity.
-/
private theorem realMobius_firstWirtinger_denominator_algebra_of_re_im
    (a c y : ℝ) (hy : (y : ℂ) ≠ 0)
    (hδ : (a : ℂ) + (c : ℂ) * (y : ℂ) * Complex.I ≠ 0) :
    let δ : ℂ := (a : ℂ) + (c : ℂ) * (y : ℂ) * Complex.I
    (-2 * (c : ℂ) / δ ^ 3) / (δ ^ 2)⁻¹ +
        Complex.I * (δ ^ 2)⁻¹ / ((y : ℂ) / (Complex.normSq δ : ℂ)) =
      Complex.I / (y : ℂ) := by
  have hnorm :
      (Complex.normSq ((a : ℂ) + (c : ℂ) * (y : ℂ) * Complex.I) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr hδ).ne'
  field_simp [hy, hδ, hnorm]
  rw [show Complex.normSq ((a : ℂ) + (c : ℂ) * (y : ℂ) * Complex.I) =
      a ^ 2 + (c * y) ^ 2 by
    simpa [mul_assoc] using Complex.normSq_add_mul_I a (c * y)]
  ring_nf
  rw [Complex.I_sq, Complex.I_pow_three]
  push_cast
  ring_nf

/-- Real Mobius transformations satisfy the denominator algebra identity.

%%handwave
name:
  The Möbius denominator satisfies the Poincare multiplier identity
statement:
  For a real Möbius map M(z) = (az+b)/(cz+d), a point p in the upper half plane, δ = cp+d, and y = Im p, one has (−2c/δ³)/(δ⁻²) + iδ⁻²/(y/|δ|²) = i/y.
proof:
  Write δ = a₀ + icy with real a₀,c,y, clear the nonzero denominators, use |δ|² = a₀²+c²y², and simplify.
-/
theorem realMobiusFirstWirtingerDenominatorAlgebraTheorem :
    RealMobiusFirstWirtingerDenominatorAlgebraTheorem := by
  intro A p
  let g : GL (Fin 2) ℝ := (A : GL (Fin 2) ℝ)
  let a : ℝ := g 1 0 * (p : ℂ).re + g 1 1
  let c : ℝ := g 1 0
  let y : ℝ := (p : ℂ).im
  have hy : (y : ℂ) ≠ 0 := by
    exact_mod_cast (show y ≠ 0 by simpa [y] using p.im_ne_zero)
  have hden :
      UpperHalfPlane.denom g p =
        (a : ℂ) + (c : ℂ) * (y : ℂ) * Complex.I := by
    dsimp [UpperHalfPlane.denom, a, c, y]
    rw [show (p : ℂ) = (p : ℂ).re + (p : ℂ).im * Complex.I from
      (Complex.re_add_im (p : ℂ)).symm]
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    push_cast
    ring_nf
  have hδ :
      (a : ℂ) + (c : ℂ) * (y : ℂ) * Complex.I ≠ 0 := by
    rw [← hden]
    exact UpperHalfPlane.denom_ne_zero g p
  have hAlg :=
    realMobius_firstWirtinger_denominator_algebra_of_re_im a c y hy hδ
  simpa [g, a, c, y, hden] using hAlg

/--
The denominator algebra identity implies the scalar real-Mobius multiplier
identity.


%%handwave
name:
  The denominator identity gives the first-Wirtinger Möbius multiplier identity
statement:
  For every real Möbius map M and p in the upper half plane, M″(p)/M′(p) + iM′(p)/Im M(p) = i/Im p.
proof:
  Substitute M′(p)=δ⁻², M″(p)=−2cδ⁻³, and Im M(p)=Im p/|δ|² into the denominator identity.
-/
theorem realMobiusFirstWirtingerMultiplierIdentityTheorem_of_denominatorAlgebra
    (hAlg : RealMobiusFirstWirtingerDenominatorAlgebraTheorem) :
    RealMobiusFirstWirtingerMultiplierIdentityTheorem := by
  intro A p
  let δ : ℂ := UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p
  let c : ℂ := ((A : GL (Fin 2) ℝ) 1 0 : ℂ)
  let y : ℂ := ((((p : ℍ) : ℂ).im : ℝ) : ℂ)
  have hα :
      deriv
        (fun w : ℂ ↦
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
        p = (δ ^ 2)⁻¹ := by
    simpa [δ] using realMobiusRepresentativeAction_deriv A p
  have hβ :
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
            w)
        p =
        -2 * c / δ ^ 3 := by
    simpa [δ, c] using realMobiusRepresentativeAction_second_deriv A p
  have hIm :
      ((((realMobiusRepresentativeAction A p : ℍ) : ℂ).im : ℝ) : ℂ) =
        y / (Complex.normSq δ : ℂ) := by
    have him_real :
        ((realMobiusRepresentativeAction A p : ℂ).im : ℝ) =
          ((p : ℂ).im : ℝ) / Complex.normSq δ := by
      simpa [realMobiusRepresentativeAction, δ] using
        (UpperHalfPlane.im_smul_eq_div_normSq (g := A) (z := p))
    simpa [y] using congrArg (fun r : ℝ ↦ (r : ℂ)) him_real
  rw [hα, hβ, hIm]
  simpa [δ, c, y] using hAlg A p

/-- Real Mobius transformations satisfy the scalar first-Wirtinger multiplier identity.

%%handwave
name:
  Real Möbius maps satisfy the first-Wirtinger multiplier identity
statement:
  For every real Möbius map M and p in the upper half plane, M″(p)/M′(p) + iM′(p)/Im M(p) = i/Im p.
proof:
  Apply the proved denominator algebra identity to the explicit derivatives and imaginary-part transformation formula.
-/
theorem realMobiusFirstWirtingerMultiplierIdentityTheorem :
    RealMobiusFirstWirtingerMultiplierIdentityTheorem :=
  realMobiusFirstWirtingerMultiplierIdentityTheorem_of_denominatorAlgebra
    realMobiusFirstWirtingerDenominatorAlgebraTheorem

/--
Algebraic form of invariance of the first-Wirtinger expression.

%%handwave
name:
  The first-Wirtinger chain-rule algebra
statement:
  Let α,β,F₁,F₂,Yp,Yq be complex numbers with α,F₁,Yp,Yq nonzero. If β/α+iα/Yq=i/Yp, then ((βF₁²+αF₂)/(αF₁)+iαF₁/Yq)/2 = (F₂/F₁+iF₁/Yp)/2.
proof:
  Split the left side into F₂/F₁+(β/α+iα/Yq)F₁, substitute the assumed multiplier identity, and clear the nonzero denominators.
-/
private theorem realMobiusPostcomposition_firstWirtinger_algebra
    {α β F₁ F₂ Yp Yq : ℂ}
    (hα : α ≠ 0) (hF₁ : F₁ ≠ 0) (hYp : Yp ≠ 0) (hYq : Yq ≠ 0)
    (hId : β / α + Complex.I * α / Yq = Complex.I / Yp) :
    ((β * F₁ ^ 2 + α * F₂) / (α * F₁) +
        Complex.I * (α * F₁) / Yq) / 2 =
      (F₂ / F₁ + Complex.I * F₁ / Yp) / 2 := by
  have hcore :
      (β * F₁ ^ 2 + α * F₂) / (α * F₁) +
          Complex.I * (α * F₁) / Yq =
        F₂ / F₁ + Complex.I * F₁ / Yp := by
    calc
      (β * F₁ ^ 2 + α * F₂) / (α * F₁) +
          Complex.I * (α * F₁) / Yq =
          F₂ / F₁ + (β / α + Complex.I * α / Yq) * F₁ := by
        field_simp [hα, hF₁, hYq]
        ring
      _ = F₂ / F₁ + Complex.I * F₁ / Yp := by
        rw [hId]
        field_simp [hYp]
  rw [hcore]

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Fixed-branch projective derivative regularity gives pointwise invariance of
the first-Wirtinger expression under real Mobius postcomposition.


%%handwave
name:
  Projective regularity gives pointwise invariance of the first-Wirtinger expression
statement:
  For a projectively regular upper-half-plane branch F, every real Möbius map M, and every domain point z, ½((M∘F)″/(M∘F)′ + i(M∘F)′/Im(M∘F)) equals ½(F″/F′ + iF′/Im F) at z.
proof:
  Use the second-order chain rule supplied by projective regularity and the Möbius multiplier identity.
-/
theorem realMobiusPostcomposition_firstWirtingerExpression
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    realMobiusPostcompositionFirstWirtingerExpression H A z =
      localUpperHalfPlaneDevelopingMapFirstWirtingerExpression H z := by
  let F₁ : ℂ := deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z
  let F₂ : ℂ :=
    deriv (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z
  let α : ℂ :=
    deriv
      (fun w : ℂ ↦
        (realMobiusRepresentativeAction A
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
      (H.upperHalfPlaneMap z)
  let β : ℂ :=
    deriv
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
          w)
      (H.upperHalfPlaneMap z)
  let Yp : ℂ := ((((H.upperHalfPlaneMap z : ℍ) : ℂ).im : ℝ) : ℂ)
  let Yq : ℂ :=
    ((((realMobiusRepresentativeAction A (H.upperHalfPlaneMap z) : ℍ) : ℂ).im : ℝ) :
      ℂ)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hα_ne : α ≠ 0 := by
    simpa [α] using
      realMobiusRepresentativeAction_deriv_ne_zero A (H.upperHalfPlaneMap z)
  have hYp_ne : Yp ≠ 0 := by
    simpa [Yp] using
      (show ((((H.upperHalfPlaneMap z : ℍ) : ℂ).im : ℂ) ≠ 0) by
        exact_mod_cast (H.upperHalfPlaneMap z).im_ne_zero)
  have hYq_ne : Yq ≠ 0 := by
    simpa [Yq] using
      (show
        ((((realMobiusRepresentativeAction A (H.upperHalfPlaneMap z) : ℍ) : ℂ).im :
          ℂ) ≠ 0) by
        exact_mod_cast
          (realMobiusRepresentativeAction A (H.upperHalfPlaneMap z)).im_ne_zero)
  have hG₁ :
      deriv
        (fun w : ℂ ↦
          (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ))
        z =
        α * F₁ := by
    simpa [α, F₁] using
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H A hz
  have hG₂ :
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
            w) z =
        β * F₁ ^ 2 + α * F₂ := by
    simpa [β, α, F₁, F₂] using
      R.realMobiusPostcompositionSecondDerivativeChainRule A hz
  have hId :
      β / α + Complex.I * α / Yq = Complex.I / Yp := by
    simpa [β, α, Yq, Yp] using
      realMobiusFirstWirtingerMultiplierIdentityTheorem A (H.upperHalfPlaneMap z)
  rw [realMobiusPostcompositionFirstWirtingerExpression,
    localUpperHalfPlaneDevelopingMapFirstWirtingerExpression, hG₁, hG₂]
  exact
    realMobiusPostcomposition_firstWirtinger_algebra
      hα_ne hF₁_ne hYp_ne hYq_ne hId

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Regular scalar Schwarzian two-jet local uniqueness.

This is the same identity-principle boundary as
`ScalarSchwarzianTwoJetValueLocalUniquenessTheorem`, but with explicit local
regularity hypotheses for the first and second derivative branches.  These
are exactly the hypotheses supplied by the upper-half-plane branch packages.

%%handwave
name:
  Local uniqueness from equal Schwarzian and matching two-jets
statement:
  This proposition asserts that two locally $C^3$ scalar maps with nonzero first derivative and equal Schwarzian, whose values and first two derivatives agree at a point, coincide on a neighborhood of that point.
-/
def ScalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem : Prop :=
  ∀ (f g : ℂ → ℂ) (U : Set ℂ) (z : ℂ),
    IsOpen U →
      z ∈ U →
        (∀ w, w ∈ U → deriv f w ≠ 0) →
          (∀ w, w ∈ U → deriv g w ≠ 0) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv f t)
                (deriv (fun t : ℂ ↦ deriv f t) w) w) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
                (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) w) w) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv g t)
                (deriv (fun t : ℂ ↦ deriv g t) w) w) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t)
                (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t) w) w) →
            (∀ w, w ∈ U → actualSchwarzian f w = actualSchwarzian g w) →
              f z = g z →
                deriv f z = deriv g z →
                  deriv (fun w : ℂ ↦ deriv f w) z =
                    deriv (fun w : ℂ ↦ deriv g w) z →
                    ∃ V : Set ℂ,
                      IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
                        ∀ w, w ∈ V → f w = g w

/-- The scalar pre-Schwarzian expression `f'' / f'`.
%%handwave
name:
  Scalar pre-Schwarzian derivative
statement:
  The pre-Schwarzian of a scalar map $f$ is $P(f)=f''/f'$.
-/
def scalarPreSchwarzian (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (fun w : ℂ ↦ deriv f w) z / deriv f z

/--
Schwarzian equality determines the pre-Schwarzian locally after the second
jet has been fixed.

This is the Riccati/linear first-order part of scalar Schwarzian uniqueness:
if two regular maps have the same Schwarzian and their pre-Schwarzians agree
at the base point, then the pre-Schwarzians agree on a neighborhood.

%%handwave
name:
  Local uniqueness of the pre-Schwarzian from the Schwarzian
statement:
  This proposition asserts that for locally $C^3$ maps with nonzero derivative and equal Schwarzian, equality of $f''/f'$ at one point forces equality of their pre-Schwarzians on a neighborhood.
-/
def ScalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem : Prop :=
  ∀ (f g : ℂ → ℂ) (U : Set ℂ) (z : ℂ),
    IsOpen U →
      z ∈ U →
        (∀ w, w ∈ U → deriv f w ≠ 0) →
          (∀ w, w ∈ U → deriv g w ≠ 0) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv f t)
                (deriv (fun t : ℂ ↦ deriv f t) w) w) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
                (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) w) w) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv g t)
                (deriv (fun t : ℂ ↦ deriv g t) w) w) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t)
                (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t) w) w) →
            (∀ w, w ∈ U → actualSchwarzian f w = actualSchwarzian g w) →
              scalarPreSchwarzian f z = scalarPreSchwarzian g z →
                ∃ V : Set ℂ,
                  IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
                    ∀ w, w ∈ V →
                      scalarPreSchwarzian f w = scalarPreSchwarzian g w

/--
Equal pre-Schwarzians and equal initial value/derivative determine the maps
locally.

This is the final integration step after the Riccati reduction.

%%handwave
name:
  Local uniqueness from equal pre-Schwarzian and one-jet
statement:
  This proposition asserts that regular maps with equal pre-Schwarzian $f''/f'$, equal value, and equal first derivative at one point coincide on a neighborhood.
-/
def ScalarPreSchwarzianValueDerivativeLocalUniquenessTheorem : Prop :=
  ∀ (f g : ℂ → ℂ) (U : Set ℂ) (z : ℂ),
    IsOpen U →
      z ∈ U →
        (∀ w, w ∈ U → deriv f w ≠ 0) →
          (∀ w, w ∈ U → deriv g w ≠ 0) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv f t)
                (deriv (fun t : ℂ ↦ deriv f t) w) w) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv g t)
                (deriv (fun t : ℂ ↦ deriv g t) w) w) →
            (∀ w, w ∈ U →
              scalarPreSchwarzian f w = scalarPreSchwarzian g w) →
                f z = g z →
                  deriv f z = deriv g z →
                    ∃ V : Set ℂ,
                      IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
                        ∀ w, w ∈ V → f w = g w

/--
Concrete integration theorem for equal pre-Schwarzians.

On a small ball, the quotient `f' / g'` has zero derivative.  It is therefore
constant by mathlib's derivative-zero identity principle; the initial first
derivative makes that constant equal to one, and a second application of the
same identity principle to `f` and `g` gives local equality.


%%handwave
name:
  Equal pre-Schwarzians and one initial one-jet determine a holomorphic map locally
statement:
  Let f and g be locally univalent holomorphic functions on an open set U, with f″/f′ = g″/g′ on U. If f(z₀)=g(z₀) and f′(z₀)=g′(z₀), then f=g on some neighborhood of z₀ contained in U.
proof:
  The quotient f′/g′ has zero derivative, hence is constant on a small ball; its initial value is one. Thus f′=g′ there, and a second derivative-zero identity argument with the initial value gives f=g.
-/
theorem scalarPreSchwarzianValueDerivativeLocalUniquenessTheorem_of_derivativeQuotient :
    ScalarPreSchwarzianValueDerivativeLocalUniquenessTheorem := by
  intro f g U z hU hz hf_ne hg_ne hf₁ hg₁ hpre hval hderiv
  have hnhds : U ∈ nhds z := hU.mem_nhds hz
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr_pos, hr_subset⟩
  let V : Set ℂ := Metric.ball z r
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hzV : z ∈ V := Metric.mem_ball_self hr_pos
  have hVpre : IsPreconnected V := (convex_ball z r).isPreconnected
  have hVsubset : V ⊆ U := hr_subset
  let q : ℂ → ℂ := fun w ↦ deriv f w / deriv g w
  have hq_differentiableOn : DifferentiableOn ℂ q V := by
    intro w hw
    exact ((hf₁ w (hVsubset hw)).differentiableAt.div
      (hg₁ w (hVsubset hw)).differentiableAt (hg_ne w (hVsubset hw))).differentiableWithinAt
  have hq_deriv_zero : V.EqOn (deriv q) 0 := by
    intro w hw
    change deriv q w = (0 : ℂ)
    have hf_at := hf₁ w (hVsubset hw)
    have hg_at := hg₁ w (hVsubset hw)
    have hg_nonzero : deriv g w ≠ 0 := hg_ne w (hVsubset hw)
    have hf_nonzero : deriv f w ≠ 0 := hf_ne w (hVsubset hw)
    have hpre_w := hpre w (hVsubset hw)
    have hdiv :
        deriv (fun t : ℂ ↦ deriv f t) w / deriv f w =
          deriv (fun t : ℂ ↦ deriv g t) w / deriv g w := by
      simpa [scalarPreSchwarzian] using hpre_w
    have hnum :
        deriv (fun t : ℂ ↦ deriv f t) w * deriv g w -
            deriv f w * deriv (fun t : ℂ ↦ deriv g t) w = 0 := by
      apply sub_eq_zero.mpr
      simpa [mul_comm] using (div_eq_div_iff hf_nonzero hg_nonzero).mp hdiv
    have hderiv_q :
        deriv q w =
          (deriv (fun t : ℂ ↦ deriv f t) w * deriv g w -
              deriv f w * deriv (fun t : ℂ ↦ deriv g t) w) /
            deriv g w ^ 2 := by
      simpa [q] using
        (deriv_div hf_at.differentiableAt hg_at.differentiableAt hg_nonzero)
    rw [hderiv_q, hnum, zero_div]
  have hq_const :
      ∀ w ∈ V, q w = q z :=
    fun w hw ↦ hVopen.is_const_of_deriv_eq_zero hVpre hq_differentiableOn
      hq_deriv_zero hw hzV
  have hq_one : ∀ w ∈ V, q w = 1 := by
    intro w hw
    calc
      q w = q z := hq_const w hw
      _ = 1 := by
        have hgz : deriv g z ≠ 0 := hg_ne z hz
        calc
          q z = deriv f z / deriv g z := rfl
          _ = deriv g z / deriv g z := by rw [hderiv]
          _ = 1 := div_self hgz
  have hderiv_eq_on : V.EqOn (deriv f) (deriv g) := by
    intro w hw
    have hg_nonzero : deriv g w ≠ 0 := hg_ne w (hVsubset hw)
    have hq_eq := hq_one w hw
    dsimp [q] at hq_eq
    exact (div_eq_one_iff_eq hg_nonzero).mp hq_eq
  have hf_diff : DifferentiableOn ℂ f V := by
    intro w hw
    exact (differentiableAt_of_deriv_ne_zero (hf_ne w (hVsubset hw))).differentiableWithinAt
  have hg_diff : DifferentiableOn ℂ g V := by
    intro w hw
    exact (differentiableAt_of_deriv_ne_zero (hg_ne w (hVsubset hw))).differentiableWithinAt
  have heq_on : V.EqOn f g :=
    hVopen.eqOn_of_deriv_eq hVpre hf_diff hg_diff hderiv_eq_on hzV hval
  exact ⟨V, hVopen, hzV, hVsubset, fun w hw ↦ heq_on hw⟩

/--
Mathlib's disk primitive theorem gives a primitive on a small ball for every
coefficient which is complex differentiable on the ambient open set.


%%handwave
name:
  A holomorphic coefficient has a primitive on a small disk
statement:
  If a is complex differentiable on an open set U and z₀∈U, then some disk B(z₀,r) lies in U and carries a holomorphic primitive A with A′=a.
proof:
  Choose a disk contained in U and apply the existence theorem for primitives on convex disks.
-/
theorem scalarPreSchwarzianRiccatiPrimitiveBallExistence_of_differentiableOn
    {a : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U)
    (ha : DifferentiableOn ℂ a U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ U ∧
      ∃ A : ℂ → ℂ,
        ∀ w, w ∈ Metric.ball z r → HasDerivAt A (a w) w := by
  rcases Metric.mem_nhds_iff.mp (hU.mem_nhds hz) with ⟨r, hr_pos, hball_subset⟩
  have ha_ball : DifferentiableOn ℂ a (Metric.ball z r) :=
    ha.mono hball_subset
  rcases ha_ball.isExactOn_ball with ⟨A, hA⟩
  exact ⟨r, hr_pos, hball_subset, A, hA⟩

/--
Zero-uniqueness for `α' = a α` when the coefficient is complex
differentiable on the ambient open set.  This combines mathlib's primitive
theorem on balls with the integrating-factor argument.


%%handwave
name:
  A holomorphic linear equation has local zero uniqueness
statement:
  Let a be complex differentiable on an open set U and let α′=aα on U. If α(z₀)=0, then α vanishes on some neighborhood of z₀ contained in U.
proof:
  Construct a primitive of a on a small disk, exponentiate its negative to obtain a nonvanishing integrating factor, and apply the product-rule argument.
-/
theorem scalarPreSchwarzianRiccatiZeroLocalUniqueness_of_differentiableCoefficient
    {a α : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U)
    (ha : DifferentiableOn ℂ a U)
    (hα_deriv : ∀ w, w ∈ U → HasDerivAt α (a w * α w) w)
    (hα₀ : α z = 0) :
    ∃ V : Set ℂ,
      IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
        ∀ w, w ∈ V → α w = 0 := by
  rcases scalarPreSchwarzianRiccatiPrimitiveBallExistence_of_differentiableOn
      hU hz ha with
    ⟨r, hr_pos, hball_subset, A, hA_deriv⟩
  let V : Set ℂ := Metric.ball z r
  let μ : ℂ → ℂ := fun w ↦ Complex.exp (-(A w))
  have hμ_ne : ∀ w, w ∈ V → μ w ≠ 0 := by
    intro w _hw
    exact Complex.exp_ne_zero (-(A w))
  have hμ_deriv : ∀ w, w ∈ V → HasDerivAt μ (-(a w) * μ w) w := by
    intro w hw
    have hneg : HasDerivAt (fun t : ℂ ↦ -(A t)) (-(a w)) w :=
      (hA_deriv w hw).neg
    have hexp := hneg.cexp
    convert hexp using 1
    ring
  let product : ℂ → ℂ := fun w ↦ μ w * α w
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hzV : z ∈ V := Metric.mem_ball_self hr_pos
  have hVpre : IsPreconnected V := (convex_ball z r).isPreconnected
  have hproduct_deriv : V.EqOn (deriv product) 0 := by
    intro w hw
    change deriv product w = (0 : ℂ)
    have hprod :
        HasDerivAt product
          ((-(a w) * μ w) * α w + μ w * (a w * α w)) w := by
      simpa [product] using
        (hμ_deriv w hw).mul (hα_deriv w (hball_subset hw))
    rw [hprod.deriv]
    ring
  have hproduct_diff : DifferentiableOn ℂ product V := by
    intro w hw
    have hprod :
        HasDerivAt product
          ((-(a w) * μ w) * α w + μ w * (a w * α w)) w := by
      simpa [product] using
        (hμ_deriv w hw).mul (hα_deriv w (hball_subset hw))
    exact hprod.differentiableAt.differentiableWithinAt
  have hproduct_const : ∀ w ∈ V, product w = product z :=
    fun w hw ↦ hVopen.is_const_of_deriv_eq_zero hVpre hproduct_diff
      hproduct_deriv hw hzV
  refine ⟨V, hVopen, hzV, hball_subset, ?_⟩
  intro w hw
  have hprod_zero : product w = 0 := by
    calc
      product w = product z := hproduct_const w hw
      _ = 0 := by simp [product, hα₀]
  exact (mul_eq_zero.mp (by simpa [product] using hprod_zero)).resolve_left
    (hμ_ne w hw)

/--
Derivative formula for the scalar pre-Schwarzian:
`(f'' / f')' = S(f) + (1 / 2) (f'' / f')^2`.


%%handwave
name:
  The derivative of the pre-Schwarzian satisfies the Schwarzian Riccati equation
statement:
  For a locally univalent C³ function f, the pre-Schwarzian P_f=f″/f′ satisfies P_f′ = S(f) + ½P_f².
proof:
  Differentiate the quotient f″/f′, substitute S(f)=f‴/f′−(3/2)(f″/f′)², and simplify using f′≠0.
-/
theorem scalarPreSchwarzian_hasDerivAt
    {f : ℂ → ℂ} {z : ℂ}
    (hf_ne : deriv f z ≠ 0)
    (hf₁ :
      HasDerivAt
        (fun t : ℂ ↦ deriv f t)
        (deriv (fun t : ℂ ↦ deriv f t) z) z)
    (hf₂ :
      HasDerivAt
        (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
        (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) z) z) :
    HasDerivAt
      (fun t : ℂ ↦ scalarPreSchwarzian f t)
      (actualSchwarzian f z + (1 / 2 : ℂ) * (scalarPreSchwarzian f z) ^ 2)
      z := by
  have hq :
      HasDerivAt
        (fun t : ℂ ↦
          deriv (fun s : ℂ ↦ deriv f s) t / deriv f t)
        ((deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) z *
              deriv f z -
            deriv (fun t : ℂ ↦ deriv f t) z *
              deriv (fun t : ℂ ↦ deriv f t) z) /
          deriv f z ^ 2)
        z :=
    hf₂.div hf₁ hf_ne
  convert hq using 1
  rw [actualSchwarzian, schwarzianExpression, scalarPreSchwarzian]
  field_simp [hf_ne]
  ring_nf

/--
Equal Schwarzians give the Riccati equation for the pre-Schwarzian
difference.


%%handwave
name:
  Equal Schwarzians give a linear equation for the pre-Schwarzian difference
statement:
  If locally univalent C³ functions f and g satisfy S(f)=S(g), then α=P_f−P_g satisfies α′=½(P_f+P_g)α.
proof:
  Subtract the two Riccati identities P′=S+½P² and factor P_f²−P_g².
-/
theorem scalarPreSchwarzian_difference_hasDerivAt_of_actualSchwarzian_eq
    {f g : ℂ → ℂ} {z : ℂ}
    (hf_ne : deriv f z ≠ 0)
    (hg_ne : deriv g z ≠ 0)
    (hf₁ :
      HasDerivAt
        (fun t : ℂ ↦ deriv f t)
        (deriv (fun t : ℂ ↦ deriv f t) z) z)
    (hf₂ :
      HasDerivAt
        (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
        (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) z) z)
    (hg₁ :
      HasDerivAt
        (fun t : ℂ ↦ deriv g t)
        (deriv (fun t : ℂ ↦ deriv g t) z) z)
    (hg₂ :
      HasDerivAt
        (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t)
        (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t) z) z)
    (hschw : actualSchwarzian f z = actualSchwarzian g z) :
    HasDerivAt
      (fun t : ℂ ↦ scalarPreSchwarzian f t - scalarPreSchwarzian g t)
      (((scalarPreSchwarzian f z + scalarPreSchwarzian g z) / 2) *
        (scalarPreSchwarzian f z - scalarPreSchwarzian g z))
      z := by
  have hfP := scalarPreSchwarzian_hasDerivAt hf_ne hf₁ hf₂
  have hgP := scalarPreSchwarzian_hasDerivAt hg_ne hg₁ hg₂
  have hsub := hfP.sub hgP
  convert hsub using 1
  ring_nf
  rw [hschw]
  ring

/--
%%handwave
name:
  Schwarzian uniqueness for the pre-Schwarzian
statement:
  Let $f$ and $g$ be locally univalent holomorphic maps on an open set $U$,
  with derivatives through order three on $U$. If
  $\{f,z\}=\{g,z\}$ on $U$ and
  $f''(z_0)/f'(z_0)=g''(z_0)/g'(z_0)$, then on some neighborhood $V$ of
  $z_0$ one has
  $$\frac{f''}{f'}=\frac{g''}{g'}.$$
proof:
  For $\alpha=f''/f'-g''/g'$ and
  $a=\tfrac12(f''/f'+g''/g')$, equality of Schwarzians gives
  $\alpha'=a\alpha$. On a small disk, a primitive of $a$ produces an
  integrating factor, so the solution with $\alpha(z_0)=0$ vanishes
  identically.
-/
theorem scalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem_proved :
    ScalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem := by
  intro f g U z hU hz hf_ne hg_ne hf₁ hf₂ hg₁ hg₂ hschw hpre₀
  let α : ℂ → ℂ := fun w ↦ scalarPreSchwarzian f w - scalarPreSchwarzian g w
  let a : ℂ → ℂ := fun w ↦ (scalarPreSchwarzian f w + scalarPreSchwarzian g w) / 2
  have hPf :
      DifferentiableOn ℂ (fun w ↦ scalarPreSchwarzian f w) U := by
    intro w hw
    exact (scalarPreSchwarzian_hasDerivAt (hf_ne w hw) (hf₁ w hw) (hf₂ w hw)).differentiableAt.differentiableWithinAt
  have hPg :
      DifferentiableOn ℂ (fun w ↦ scalarPreSchwarzian g w) U := by
    intro w hw
    exact (scalarPreSchwarzian_hasDerivAt (hg_ne w hw) (hg₁ w hw) (hg₂ w hw)).differentiableAt.differentiableWithinAt
  have ha : DifferentiableOn ℂ a U := by
    intro w hw
    exact ((hPf w hw).add (hPg w hw)).div_const 2
  have hα_deriv : ∀ w, w ∈ U → HasDerivAt α (a w * α w) w := by
    intro w hw
    simpa [α, a] using
      (scalarPreSchwarzian_difference_hasDerivAt_of_actualSchwarzian_eq
        (hf_ne w hw) (hg_ne w hw)
        (hf₁ w hw) (hf₂ w hw) (hg₁ w hw) (hg₂ w hw)
        (hschw w hw))
  have hα₀ : α z = 0 := by
    simpa [α] using sub_eq_zero.mpr hpre₀
  rcases scalarPreSchwarzianRiccatiZeroLocalUniqueness_of_differentiableCoefficient
      hU hz ha hα_deriv hα₀ with
    ⟨V, hVopen, hzV, hVsubset, hα_zero⟩
  refine ⟨V, hVopen, hzV, hVsubset, ?_⟩
  intro w hw
  have h := hα_zero w hw
  simpa [α] using sub_eq_zero.mp h

/--
The Riccati pre-Schwarzian reduction plus the final integration step imply
the regular scalar Schwarzian two-jet uniqueness theorem.


%%handwave
name:
  Equal Schwarzians and an equal two-jet determine a regular map locally
statement:
  Let f and g be locally univalent C³ functions on an open set U. If S(f)=S(g) on U and f, f′, and f″ agree with g, g′, and g″ at z₀, then f=g on some neighborhood of z₀.
proof:
  The equal two-jet gives equal pre-Schwarzians at z₀; Riccati uniqueness makes them equal nearby, and the derivative-quotient argument integrates this equality using the common value and first derivative.
-/
theorem scalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem_of_preSchwarzian
    (hPre :
      ScalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem)
    (hInt :
      ScalarPreSchwarzianValueDerivativeLocalUniquenessTheorem) :
    ScalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem := by
  intro f g U z hU hz hf_ne hg_ne hf₁ hf₂ hg₁ hg₂ hschw hval hderiv hsecond
  have hpre₀ : scalarPreSchwarzian f z = scalarPreSchwarzian g z := by
    unfold scalarPreSchwarzian
    rw [hderiv, hsecond]
  rcases hPre f g U z hU hz hf_ne hg_ne hf₁ hf₂ hg₁ hg₂ hschw hpre₀ with
    ⟨W, hWopen, hzW, hWsubset, hpreW⟩
  have hf_ne_W : ∀ w, w ∈ W → deriv f w ≠ 0 := fun w hw ↦ hf_ne w (hWsubset hw)
  have hg_ne_W : ∀ w, w ∈ W → deriv g w ≠ 0 := fun w hw ↦ hg_ne w (hWsubset hw)
  have hf₁_W :
      ∀ w, w ∈ W →
        HasDerivAt
          (fun t : ℂ ↦ deriv f t)
          (deriv (fun t : ℂ ↦ deriv f t) w) w :=
    fun w hw ↦ hf₁ w (hWsubset hw)
  have hg₁_W :
      ∀ w, w ∈ W →
        HasDerivAt
          (fun t : ℂ ↦ deriv g t)
          (deriv (fun t : ℂ ↦ deriv g t) w) w :=
    fun w hw ↦ hg₁ w (hWsubset hw)
  rcases hInt f g W z hWopen hzW hf_ne_W hg_ne_W hf₁_W hg₁_W hpreW hval hderiv with
    ⟨V, hVopen, hzV, hVsubsetW, hVeq⟩
  exact ⟨V, hVopen, hzV, fun w hw ↦ hWsubset (hVsubsetW hw), hVeq⟩

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Fixed-branch projective derivative regularity identifies the actual Schwarzian
of that branch with its stored symbolic Schwarzian coefficient.


%%handwave
name:
  A projectively regular developing branch has its prescribed Schwarzian
statement:
  For every projectively regular developing branch F with coefficient q, S(F)(z)=q(z) at every point z of its domain.
proof:
  Replace F″ and F‴ by the stored projective derivative fields and use their defining Schwarzian relation.
-/
theorem actualSchwarzian_eq_coefficient
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    {z : ℂ} (hz : z ∈ H.domain) :
    actualSchwarzian (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z =
      S.coefficient z := by
  rw [actualSchwarzian, schwarzianExpression,
    H.upperHalfPlane_deriv_eq_projectiveDeriv z hz,
    (R.firstDerivative_hasDerivAt hz).deriv,
    (R.secondDerivative_hasDerivAt hz).deriv]
  rw [← schwarzianExpression]
  exact H.projective.schwarzian_eq_coefficient z hz

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Real Mobius transformations have zero actual Schwarzian in their affine
upper-half-plane coordinate.

%%handwave
name:
  Vanishing Schwarzian of real Möbius transformations
statement:
  This proposition asserts that every $A\in\mathrm{PSL}_2(\mathbb R)$ has $S(A)=0$ at every point of $\mathbb H$ in the affine complex coordinate.
-/
def RealMobiusActualSchwarzianZeroTheorem : Prop :=
  ∀ (A : RealMobiusRepresentative) (p : ℍ),
    actualSchwarzian
      (fun w : ℂ ↦
        (realMobiusRepresentativeAction A
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
      p = 0

/-- Real Mobius transformations have zero actual Schwarzian.

%%handwave
name:
  Every real Möbius transformation has zero Schwarzian
statement:
  For M(z)=(az+b)/(cz+d) with ad−bc≠0, one has S(M)=M‴/M′−(3/2)(M″/M′)²=0 at every point of the upper half plane.
proof:
  Insert the explicit first three derivatives of M, cancel the nonzero denominator, and simplify.
-/
theorem realMobiusActualSchwarzianZeroTheorem :
    RealMobiusActualSchwarzianZeroTheorem := by
  intro A p
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let δ : ℂ := UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p
  let c : ℂ := ((A : GL (Fin 2) ℝ) 1 0 : ℂ)
  have hδ_ne : δ ≠ 0 := by
    simpa [δ] using UpperHalfPlane.denom_ne_zero (A : GL (Fin 2) ℝ) p
  have h₁ : deriv M p = (δ ^ 2)⁻¹ := by
    simpa [M, δ] using realMobiusRepresentativeAction_deriv A p
  have h₂ :
      deriv (fun w : ℂ ↦ deriv M w) p = -2 * c / δ ^ 3 := by
    simpa [M, δ, c] using realMobiusRepresentativeAction_second_deriv A p
  have h₃ :
      deriv (fun w : ℂ ↦ deriv (fun t : ℂ ↦ deriv M t) w) p =
        6 * c ^ 2 / δ ^ 4 := by
    simpa [M, δ, c] using realMobiusRepresentativeAction_third_deriv A p
  rw [actualSchwarzian, schwarzianExpression, h₁, h₂, h₃]
  field_simp [hδ_ne]
  ring

/--
Algebraic cancellation behind Schwarzian invariance under postcomposition.

%%handwave
name:
  The third-order Schwarzian chain-rule cancellation
statement:
  Let α,β,γ be the first three derivatives of an outer map and F₁,F₂,F₃ those of an inner map, with αF₁ ≠ 0. If γ/α−(3/2)(β/α)²=0, then the Schwarzian expression formed from αF₁, βF₁²+αF₂, and γF₁³+3βF₁F₂+αF₃ equals F₃/F₁−(3/2)(F₂/F₁)².
proof:
  Expand the left side, isolate the outer Schwarzian factor (γ/α−(3/2)(β/α)²)F₁², and use its vanishing.
-/
private theorem actualSchwarzian_postcomposition_algebra
    {α β γ F₁ F₂ F₃ : ℂ}
    (hα : α ≠ 0) (hF₁ : F₁ ≠ 0)
    (hM : γ / α - 3 / 2 * (β / α) ^ 2 = 0) :
    (γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃) / (α * F₁) -
        3 / 2 * ((β * F₁ ^ 2 + α * F₂) / (α * F₁)) ^ 2 =
      F₃ / F₁ - 3 / 2 * (F₂ / F₁) ^ 2 := by
  have hαF₁ : α * F₁ ≠ 0 := mul_ne_zero hα hF₁
  have hsplit :
      (γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃) / (α * F₁) -
          3 / 2 * ((β * F₁ ^ 2 + α * F₂) / (α * F₁)) ^ 2 =
        F₃ / F₁ + (γ / α - 3 / 2 * (β / α) ^ 2) * F₁ ^ 2 -
          3 / 2 * (F₂ / F₁) ^ 2 := by
    field_simp [hα, hF₁, hαF₁]
    ring
  rw [hsplit, hM]
  ring

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Fixed-branch projective derivative regularity proves actual-Schwarzian
invariance under postcomposition by a real Mobius transformation.


%%handwave
name:
  Projective regularity proves Möbius invariance of the actual Schwarzian
statement:
  For a projectively regular upper-half-plane branch F and every real Möbius map M, S(M∘F)(z)=S(F)(z) throughout the branch domain.
proof:
  Use projective regularity to justify the second- and third-order chain rules, then apply the vanishing Schwarzian of M.
-/
theorem realMobiusPostcomposition_actualSchwarzian
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    actualSchwarzian
      (fun w : ℂ ↦
        (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ))
      z =
    actualSchwarzian (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z := by
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let G : ℂ → ℂ :=
    fun w ↦ (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv (fun w ↦ deriv F w) z
  let F₃ : ℂ := deriv (fun w ↦ deriv (fun t ↦ deriv F t) w) z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv (fun w ↦ deriv M w) (F z)
  let γ : ℂ := deriv (fun w ↦ deriv (fun t ↦ deriv M t) w) (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hα_ne : α ≠ 0 := by
    simpa [α, M, F] using
      realMobiusRepresentativeAction_deriv_ne_zero A (H.upperHalfPlaneMap z)
  have hG₁ :
      deriv G z = α * F₁ := by
    simpa [G, M, F, α, F₁] using
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H A hz
  have hG₂ :
      deriv (fun w ↦ deriv G w) z = β * F₁ ^ 2 + α * F₂ := by
    simpa [G, M, F, β, α, F₁, F₂] using
      R.realMobiusPostcompositionSecondDerivativeChainRule A hz
  have hG₃ :
      deriv (fun w ↦ deriv (fun t ↦ deriv G t) w) z =
        γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃ := by
    simpa [G, M, F, γ, β, α, F₁, F₂, F₃] using
      R.realMobiusPostcompositionThirdDerivativeChainRule A hz
  have hM :
      γ / α - 3 / 2 * (β / α) ^ 2 = 0 := by
    have h := realMobiusActualSchwarzianZeroTheorem A (H.upperHalfPlaneMap z)
    simpa [actualSchwarzian, schwarzianExpression, M, F, γ, β, α] using h
  rw [actualSchwarzian, schwarzianExpression, hG₁, hG₂, hG₃]
  exact actualSchwarzian_postcomposition_algebra hα_ne hF₁_ne hM

/--
Fixed-branch projective derivative regularity gives the Schwarzian equation
for a real-Mobius postcomposition of a metric-recovering branch.


%%handwave
name:
  A Möbius postcomposition satisfies the same Schwarzian equation
statement:
  If a projectively regular developing branch F has Schwarzian coefficient q and M is real Möbius, then S(M∘F)=q throughout the branch domain.
proof:
  Combine S(M∘F)=S(F) with S(F)=q.
-/
theorem realMobiusPostcomposition_actualSchwarzian_eq_coefficient
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    actualSchwarzian
      (fun w : ℂ ↦
        (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ))
      z =
    S.coefficient z := by
  rw [R.realMobiusPostcomposition_actualSchwarzian A hz]
  exact R.actualSchwarzian_eq_coefficient hz

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

end

end JJMath
