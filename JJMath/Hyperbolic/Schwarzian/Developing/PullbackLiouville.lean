import JJMath.Hyperbolic.Schwarzian.Developing.NormalForms

/-!
# Split Schwarzian developing-map constructions
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

/--
Build the local conformal factor carried by an explicit pullback logarithmic
density on a normalized upper-half-plane branch.

%%handwave
name:
  Conformal factor from an explicit pullback logarithmic density
statement:
  A $C^3$ real function $v$ on the domain of a normalized branch defines the local conformal factor with coordinate domain that branch domain and logarithmic density $v$.
-/
def pullbackConformalFactorFromLogDensity
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (logDensity : ℂ → ℝ)
    (logDensity_contDiffOn : ContDiffOn ℝ 3 logDensity N.domain)
    (twice_differentiable_on_domain : ContDiffOn ℝ 2 logDensity N.domain) :
    LocalConformalFactor where
  coordinateDomain := N.domain
  isOpen_coordinateDomain := by
    simpa [LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
      LocalUpperHalfPlaneProjectiveNormalization.domain] using
      N.normalized.projective.isOpen_domain
  logDensity := logDensity
  logDensity_contDiffOn := logDensity_contDiffOn
  twice_differentiable_on_domain := twice_differentiable_on_domain

/--
Concrete Poincare pullback formula data for a normalized `ℍ`-valued branch.

This is a sharper version of `LocalHyperbolicPullbackLiouvilleCandidate`: it
starts from an explicit logarithmic density function on the normalized domain.
Analytically this function should be
`log |F'| - log Im(F)`, where `F` is the normalized upper-half-plane branch.
The structure records the exact obligations needed to package this formula as
a competing Liouville factor.
-/
structure LocalHyperbolicPullbackLiouvilleFormulaData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The logarithmic density of the Poincare pullback factor. -/
  logDensity : ℂ → ℝ
  /-- The pullback logarithmic density is `C^3` on the normalized domain. -/
  logDensity_contDiffOn : ContDiffOn ℝ 3 logDensity N.domain
  /-- The pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : ContDiffOn ℝ 2 logDensity N.domain
  /-- The pullback logarithmic density solves the hyperbolic Liouville equation. -/
  solvesLiouville :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian logDensity z = Real.exp (2 * logDensity z)
  /-- Its squared density is the Poincare pullback squared density. -/
  densitySq_eq_pullback :
    ∀ z, z ∈ N.domain →
      Real.exp (2 * logDensity z) =
        Complex.normSq (N.normalized.projective.affineMapDeriv z) /
          ((N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2)
  /--
  The Schwarzian coefficient computed from this formula agrees with the
  original coefficient `S.coefficient` on the local domain.
  -/
  same_schwarzian_coefficient :
    ∀ z, z ∈ N.domain →
      LocalSchwarzianData.metricSchwarzianCoefficient
          (pullbackConformalFactorFromLogDensity N logDensity
            logDensity_contDiffOn twice_differentiable_on_domain).halfSchwarzianCoefficient
          z =
        S.coefficient z
  /-- The two squared densities agree at the base point. -/
  base_densitySq_eq :
    Real.exp (2 * logDensity z₀) = u.densitySq z₀
  /--
  The first Wirtinger derivative of this formula agrees with the prescribed
  canonical derivative `N.jet.uZ`, hence with `u_z z₀`.
  -/
  base_uZ_eq :
    frechetDZValue (fun z : ℂ ↦ (logDensity z : ℂ)) z₀ = N.jet.uZ

namespace LocalHyperbolicPullbackLiouvilleFormulaData

/-- Package the explicit pullback formula as a local conformal factor.
%%handwave
name:
  Conformal factor carried by pullback formula data
statement:
  Explicit Poincaré pullback formula data determine the local conformal factor whose logarithmic density is the stored pullback density.
-/
def conformalFactor
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicPullbackLiouvilleFormulaData N) :
    LocalConformalFactor :=
  pullbackConformalFactorFromLogDensity N P.logDensity
    P.logDensity_contDiffOn P.twice_differentiable_on_domain

/--
%%handwave
name: Base Wirtinger derivative of an explicit pullback factor
statement:
  Let $u$ be a local conformal factor, let $F$ be a normalized upper-half-plane branch based at $z_0$, and let $v$ be explicit pullback formula data whose prescribed base derivative is the normalized two-jet. Then the conformal factor with logarithmic density $v$ satisfies $\partial_z v(z_0)=\partial_z u(z_0)$.
proof:
  The formula data identify $\partial_z v(z_0)$ with the derivative component of the normalized two-jet, while normalization identifies that component with $\partial_z u(z_0)$.
-/
theorem conformalFactor_wirtingerZ_base_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicPullbackLiouvilleFormulaData N) :
    P.conformalFactor.wirtingerZ z₀ = u.wirtingerZ z₀ := by
  calc
    P.conformalFactor.wirtingerZ z₀ = N.jet.uZ := by
      simpa [LocalConformalFactor.wirtingerZ,
        LocalConformalFactor.complexLogDensity,
        LocalHyperbolicPullbackLiouvilleFormulaData.conformalFactor] using
        P.base_uZ_eq
    _ = u.wirtingerZ z₀ :=
      N.jet_uZ_eq_wirtingerZ

end LocalHyperbolicPullbackLiouvilleFormulaData

/--
Canonical Poincare pullback formula data.

Compared with `LocalHyperbolicPullbackLiouvilleFormulaData`, this package fixes
the logarithmic density to be
`(1 / 2) * log (|F'|² / (Im F)²)`.  Consequently the squared-density pullback
formula is no longer an assumption: it follows from positivity of the
Poincare density and `exp_log`.
-/
structure LocalHyperbolicCanonicalPullbackLiouvilleFormulaData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The upper-half-plane branch is `C^3` as a complex-valued function. -/
  upperHalfPlaneMap_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain
  /-- The derivative branch is `C^3` as a complex-valued function. -/
  affineMapDeriv_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain
  /-- The canonical pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : N.PullbackLogDensityTwiceDifferentiable
  /--
  The remaining Laplacian calculation for the canonical Poincare pullback:
  `Δ v = |F'|² / (Im F)²`.

  Since Lean proves separately that `exp (2v)` is the same pullback density,
  this field implies the hyperbolic Liouville equation.
  -/
  laplacian_eq_pullbackDensitySq :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian N.pullbackLogDensity z =
        N.pullbackDensitySq z
  /--
  The Schwarzian coefficient computed from this canonical formula agrees with
  the original coefficient `S.coefficient` on the local domain.
  -/
  same_schwarzian_coefficient :
    N.PullbackSchwarzianCompatibility
      upperHalfPlaneMap_contDiffOn affineMapDeriv_contDiffOn N.PullbackLogDensityTwiceDifferentiable
  /--
  The base derivative of the canonical pullback formula has the expected
  expression in terms of the normalized branch two-jet, reduced to numerator
  and denominator derivative calculations for the squared density.
  -/
  affineMapDeriv_hasDerivAt_base :
    HasDerivAt (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z)
      (N.normalized.projective.affineMapSecondDeriv z₀) z₀
  /-- The upper-half-plane branch has the expected genuine derivative at the base point. -/
  upperHalfPlaneMap_hasDerivAt_base :
    HasDerivAt (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ))
      (N.normalized.projective.affineMapDeriv z₀) z₀

namespace LocalHyperbolicCanonicalPullbackLiouvilleFormulaData

/--
%%handwave
name: Smoothness of the canonical pullback logarithmic density
statement:
  If a normalized upper-half-plane branch $F$ and its derivative $F'$ are $C^3$ on a domain $\Omega$, then $v=\frac12\log\bigl(|F'|^2/(\operatorname{Im}F)^2\bigr)$ is $C^3$ on $\Omega$.
proof:
  Apply the smoothness theorem for the logarithm of the Poincare pullback density to the given $C^3$ branch and derivative.
-/
theorem logDensity_contDiffOn
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N) :
    ContDiffOn ℝ 3 N.pullbackLogDensity N.domain :=
  N.pullbackLogDensity_contDiffOn_of_branch_contDiffOn
    P.upperHalfPlaneMap_contDiffOn P.affineMapDeriv_contDiffOn

/--
%%handwave
name: Liouville equation for the canonical pullback density
statement:
  Let $F:\Omega\to\mathbb H$ be a normalized branch and set $v=\frac12\log\bigl(|F'|^2/(\operatorname{Im}F)^2\bigr)$. If $\Delta v=|F'|^2/(\operatorname{Im}F)^2$ on $\Omega$, then $\Delta v=e^{2v}$ on $\Omega$.
proof:
  Substitute the assumed Laplacian identity and use the canonical identity $e^{2v}=|F'|^2/(\operatorname{Im}F)^2$.
-/
theorem solvesLiouville
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N) :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian N.pullbackLogDensity z =
        Real.exp (2 * N.pullbackLogDensity z) := by
  intro z hz
  rw [P.laplacian_eq_pullbackDensitySq z hz]
  exact (N.exp_two_pullbackLogDensity_eq_pullbackDensitySq hz).symm

/--
%%handwave
name: Differentiability of the pullback numerator at the base point
statement:
  If the derivative branch $F'$ has complex derivative $F''(z_0)$ at $z_0$, then the real-valued function $z\mapsto |F'(z)|^2$ is real differentiable at $z_0$.
proof:
  Complex differentiability of $F'$ implies real differentiability, and the squared norm is a real-differentiable polynomial in the real and imaginary parts.
-/
theorem numerator_differentiableAt_base
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N) :
    DifferentiableAt ℝ
      (fun z : ℂ ↦ Complex.normSq (N.normalized.projective.affineMapDeriv z)) z₀ :=
  N.numerator_differentiableAt_base_of_affineMapDeriv_hasDerivAt
    P.affineMapDeriv_hasDerivAt_base

/--
%%handwave
name: Wirtinger derivative of the pullback numerator at the base point
statement:
  For a normalized branch with $(F')'(z_0)=F''(z_0)$ and positive real $F'(z_0)$, one has $\partial_z|F'|^2(z_0)=|F'(z_0)|^2F''(z_0)/F'(z_0)$.
proof:
  Apply the squared-norm Wirtinger derivative formula to the genuine derivative of $F'$, then use that the normalized value $F'(z_0)$ is positive real.
-/
theorem numerator_base_derivative_formula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N) :
    N.PullbackDensitySqBaseNumeratorDerivativeFormula :=
  N.numerator_base_derivative_formula_of_affineMapDeriv_hasDerivAt
    P.affineMapDeriv_hasDerivAt_base

/--
%%handwave
name: Differentiability of the pullback denominator at the base point
statement:
  If an upper-half-plane branch $F$ has complex derivative $F'(z_0)$ at $z_0$, then $z\mapsto(\operatorname{Im}F(z))^2$ is real differentiable at $z_0$.
proof:
  The imaginary-part map and squaring are real differentiable, so the claim follows by composition with the real-differentiable map $F$.
-/
theorem denominator_differentiableAt_base
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N) :
    DifferentiableAt ℝ
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2) z₀ :=
  N.denominator_differentiableAt_base_of_upperHalfPlaneMap_hasDerivAt
    P.upperHalfPlaneMap_hasDerivAt_base

/--
%%handwave
name: Wirtinger derivative of the pullback denominator at the base point
statement:
  For a normalized branch satisfying $F(z_0)=i$ and $F'(z_0)$ equal to its prescribed complex derivative, $\partial_z(\operatorname{Im}F)^2(z_0)=-iF'(z_0)$.
proof:
  Differentiate the squared imaginary part by the Wirtinger chain rule and substitute $\operatorname{Im}F(z_0)=1$.
-/
theorem denominator_base_derivative_formula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N) :
    N.PullbackDensitySqBaseDenominatorDerivativeFormula :=
  N.denominator_base_derivative_formula_of_upperHalfPlaneMap_hasDerivAt
    P.upperHalfPlaneMap_hasDerivAt_base

/--
%%handwave
name: Base derivative of the Poincare pullback squared density
statement:
  For $\rho=|F'|^2/(\operatorname{Im}F)^2$ at a normalized base point $F(z_0)=i$, the branch derivative hypotheses imply $\partial_z\rho(z_0)=\rho(z_0)\bigl(F''(z_0)/F'(z_0)+iF'(z_0)\bigr)$.
proof:
  Apply the quotient rule to the established numerator and denominator derivatives, using their differentiability and the positivity of $(\operatorname{Im}F(z_0))^2$.
-/
theorem densitySq_base_derivative_formula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N) :
    N.PullbackDensitySqBaseDerivativeFormula :=
  N.pullbackDensitySq_base_derivativeFormula_of_num_den
    P.numerator_differentiableAt_base
    P.denominator_differentiableAt_base
    P.numerator_base_derivative_formula
    P.denominator_base_derivative_formula

/--
%%handwave
name: Differentiability of the Poincare pullback squared density
statement:
  If $|F'|^2$ and $(\operatorname{Im}F)^2$ are real differentiable at $z_0$ and $F(z_0)\in\mathbb H$, then $\rho=|F'|^2/(\operatorname{Im}F)^2$ is real differentiable at $z_0$.
proof:
  The denominator is positive at an upper-half-plane value, hence nonzero; differentiability follows from the product and reciprocal rules.
-/
theorem densitySq_differentiableAt_base
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N) :
    DifferentiableAt ℝ N.pullbackDensitySq z₀ := by
  change DifferentiableAt ℝ
    (fun z : ℂ ↦
      Complex.normSq (N.normalized.projective.affineMapDeriv z) /
        ((N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2)) z₀
  simpa [div_eq_mul_inv] using
    P.numerator_differentiableAt_base.mul
      (P.denominator_differentiableAt_base.inv
        (N.upperHalfPlaneMap_im_sq_pos z₀).ne')

/--
%%handwave
name: Base derivative of the canonical pullback logarithmic density
statement:
  Let $v=\frac12\log\rho$, where $\rho=|F'|^2/(\operatorname{Im}F)^2$. At a normalized base point, the squared-density derivative formula implies $\partial_zv(z_0)=\frac12\bigl(F''(z_0)/F'(z_0)+iF'(z_0)\bigr)$.
proof:
  Differentiate $v=\frac12\log\rho$, use positivity of $\rho(z_0)$, and substitute the established formula for $\partial_z\rho(z_0)$.
-/
theorem base_derivative_formula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N) :
    N.PullbackLogDensityBaseDerivativeFormula :=
  N.pullbackLogDensity_base_derivativeFormula_of_densitySqDerivative
    P.densitySq_differentiableAt_base P.densitySq_base_derivative_formula

/--
%%handwave
name: Canonical pullback derivative equals the normalized jet
statement:
  At the normalized base point $z_0$, the canonical pullback logarithmic density satisfies $\partial_zv(z_0)=u_z^{\mathrm{jet}}$, the derivative prescribed by the hyperbolic two-jet.
proof:
  Substitute the base derivative formula $\partial_zv(z_0)=\frac12(F''/F'+iF')$ and use the defining algebraic identity for the normalized hyperbolic two-jet.
-/
theorem base_uZ_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N) :
    frechetDZValue (fun z : ℂ ↦ (N.pullbackLogDensity z : ℂ)) z₀ = N.jet.uZ :=
  N.pullbackLogDensity_base_uZ_eq_of_derivativeFormula P.base_derivative_formula

/--
Forget the canonical choice of logarithmic density, retaining the older
explicit formula package.

%%handwave
name:
  Explicit Liouville formula from the canonical pullback
statement:
  Canonical pullback data for $v=\tfrac12\log(|F'|^2/(\operatorname{Im}F)^2)$ yield explicit Liouville formula data with the same density, Schwarzian, and normalized base one-jet.
-/
def toFormulaData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N) :
    LocalHyperbolicPullbackLiouvilleFormulaData N where
  logDensity := N.pullbackLogDensity
  logDensity_contDiffOn := P.logDensity_contDiffOn
  twice_differentiable_on_domain := P.twice_differentiable_on_domain
  solvesLiouville := P.solvesLiouville
  densitySq_eq_pullback := by
    intro z hz
    simpa [LocalHyperbolicTwoJetUpperHalfPlaneNormalization.pullbackDensitySq]
      using N.exp_two_pullbackLogDensity_eq_pullbackDensitySq hz
  same_schwarzian_coefficient :=
    by
      intro z hz
      simpa [pullbackConformalFactorFromLogDensity,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization.PullbackSchwarzianCompatibility,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization.pullbackConformalFactor]
        using P.same_schwarzian_coefficient z hz
  base_densitySq_eq := N.exp_two_pullbackLogDensity_base_eq_densitySq
  base_uZ_eq :=
    P.base_uZ_eq

/--
%%handwave
name: Schwarzian compatibility of the forgotten canonical pullback factor
statement:
  Let $S$ be the prescribed Schwarzian coefficient and let $v$ be the canonical Poincare pullback logarithmic density on $\Omega$. After forgetting the canonical presentation, the metric Schwarzian of $v$ still equals $S(z)$ for every $z\in\Omega$.
proof:
  The forgetful construction leaves the pullback conformal factor unchanged, so the conclusion is exactly the Schwarzian-compatibility assumption of the canonical formula data.
-/
theorem toFormulaData_metricSchwarzian_eq_coefficient
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N) :
    ∀ z, z ∈ N.domain →
      LocalSchwarzianData.metricSchwarzianCoefficient
        P.toFormulaData.conformalFactor.halfSchwarzianCoefficient z =
      S.coefficient z := by
  intro z hz
  simpa [LocalHyperbolicCanonicalPullbackLiouvilleFormulaData.toFormulaData,
    LocalHyperbolicPullbackLiouvilleFormulaData.conformalFactor,
    LocalHyperbolicTwoJetUpperHalfPlaneNormalization.PullbackSchwarzianCompatibility,
    LocalHyperbolicTwoJetUpperHalfPlaneNormalization.pullbackConformalFactor]
    using P.same_schwarzian_coefficient z hz

end LocalHyperbolicCanonicalPullbackLiouvilleFormulaData

namespace LocalHyperbolicTwoJetUpperHalfPlaneNormalization

/--
%%handwave
name: Real Laplacian identity from the mixed Wirtinger formula
statement:
  Let $v=\frac12\log\bigl(|F'|^2/(\operatorname{Im}F)^2\bigr)$ on $\Omega$. If $\partial_{\bar z}\partial_zv=\frac14|F'|^2/(\operatorname{Im}F)^2$ on $\Omega$, then $\Delta v=|F'|^2/(\operatorname{Im}F)^2$ there.
proof:
  For a twice differentiable real-valued function, $\partial_{\bar z}\partial_zv=\frac14\Delta v$. Equate this with the assumed mixed Wirtinger formula, cancel the nonzero scalar $1/4$ in $\mathbb C$, and use injectivity of the real embedding.
-/
theorem laplacian_eq_pullbackDensitySq_of_mixedWirtingerLaplacianFormula
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    {upperHalfPlaneMap_contDiffOn :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain}
    {affineMapDeriv_contDiffOn :
      ContDiffOn ℝ 3
        (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain}
    {twice_differentiable_on_domain : Prop}
    (hmixed :
      N.PullbackMixedWirtingerLaplacianFormula
        upperHalfPlaneMap_contDiffOn affineMapDeriv_contDiffOn
        twice_differentiable_on_domain) :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian N.pullbackLogDensity z =
        N.pullbackDensitySq z := by
  intro z hz
  let V :=
    N.pullbackConformalFactor
      upperHalfPlaneMap_contDiffOn affineMapDeriv_contDiffOn
      twice_differentiable_on_domain
  have hbridge :
      V.wirtingerZBar z =
        (1 / 4 : ℂ) *
          (Laplacian.laplacian N.pullbackLogDensity z : ℂ) := by
    simpa [V, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.pullbackConformalFactor]
      using V.wirtingerZBar_eq_laplacian z hz
  have hscaled :
      (1 / 4 : ℂ) *
          (Laplacian.laplacian N.pullbackLogDensity z : ℂ) =
        (1 / 4 : ℂ) * (N.pullbackDensitySq z : ℂ) := by
    calc
      (1 / 4 : ℂ) *
          (Laplacian.laplacian N.pullbackLogDensity z : ℂ) =
          V.wirtingerZBar z := hbridge.symm
      _ = (1 / 4 : ℂ) * (N.pullbackDensitySq z : ℂ) :=
          hmixed z hz
  have hcomplex :
      (Laplacian.laplacian N.pullbackLogDensity z : ℂ) =
        (N.pullbackDensitySq z : ℂ) :=
    mul_left_cancel₀ (show (1 / 4 : ℂ) ≠ 0 by norm_num) hscaled
  exact Complex.ofReal_injective hcomplex

end LocalHyperbolicTwoJetUpperHalfPlaneNormalization

/--
Core analytic data for the canonical Poincare pullback formula.

This is the sharpened remaining pullback boundary.  The two real geometric
calculations are:
* `laplacian_eq_pullbackDensitySq`, proving the curvature/Liouville identity;
* `metricSchwarzian_eq_branchSchwarzian`, proving that the metric Schwarzian
  of the Poincare pullback is the ordinary branch Schwarzian.

The rest of the canonical formula package is then obtained by previously
proved calculus and two-jet algebra.
-/
structure LocalHyperbolicCanonicalPullbackCoreData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The upper-half-plane branch is `C^3` as a complex-valued function. -/
  upperHalfPlaneMap_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain
  /-- The derivative branch is `C^3` as a complex-valued function. -/
  affineMapDeriv_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain
  /-- The canonical pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : N.PullbackLogDensityTwiceDifferentiable
  /-- The geometric Laplacian calculation for the Poincare pullback density. -/
  laplacian_eq_pullbackDensitySq :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian N.pullbackLogDensity z =
        N.pullbackDensitySq z
  /--
  The metric Schwarzian of the canonical pullback conformal factor is the
  ordinary branch Schwarzian.
  -/
  metricSchwarzian_eq_branchSchwarzian :
    N.PullbackMetricSchwarzianEqualsBranchSchwarzian
      upperHalfPlaneMap_contDiffOn affineMapDeriv_contDiffOn N.PullbackLogDensityTwiceDifferentiable
  /-- The derivative branch has the expected genuine derivative at the base point. -/
  affineMapDeriv_hasDerivAt_base :
    HasDerivAt (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z)
      (N.normalized.projective.affineMapSecondDeriv z₀) z₀
  /-- The upper-half-plane branch has the expected genuine derivative at the base point. -/
  upperHalfPlaneMap_hasDerivAt_base :
    HasDerivAt (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ))
      (N.normalized.projective.affineMapDeriv z₀) z₀

namespace LocalHyperbolicCanonicalPullbackCoreData

/--
Core pullback data imply the canonical pullback Liouville formula package.

%%handwave
name:
  Canonical formula data from core pullback identities
statement:
  Smoothness, the Poincaré Laplacian identity, metric-Schwarzian compatibility, and the normalized base derivatives together form the canonical pullback Liouville formula package.
-/
def toFormulaData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (C : LocalHyperbolicCanonicalPullbackCoreData N) :
    LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N where
  upperHalfPlaneMap_contDiffOn := C.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := C.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := C.twice_differentiable_on_domain
  laplacian_eq_pullbackDensitySq := C.laplacian_eq_pullbackDensitySq
  same_schwarzian_coefficient :=
    N.pullbackSchwarzianCompatibility_of_metricSchwarzian_eq_branchSchwarzian
      C.metricSchwarzian_eq_branchSchwarzian
  affineMapDeriv_hasDerivAt_base := C.affineMapDeriv_hasDerivAt_base
  upperHalfPlaneMap_hasDerivAt_base := C.upperHalfPlaneMap_hasDerivAt_base

end LocalHyperbolicCanonicalPullbackCoreData

/--
Core canonical pullback data with the Poincare Laplacian calculation reduced
to its mixed-Wirtinger form.

Lean then obtains the real Laplacian field from the general
`∂_{\bar z} ∂_z = (1 / 4) Δ` bridge for local conformal factors.
-/
structure LocalHyperbolicCanonicalPullbackMixedWirtingerLaplacianData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The upper-half-plane branch is `C^3` as a complex-valued function. -/
  upperHalfPlaneMap_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain
  /-- The derivative branch is `C^3` as a complex-valued function. -/
  affineMapDeriv_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain
  /-- The canonical pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : N.PullbackLogDensityTwiceDifferentiable
  /-- Mixed-Wirtinger form of the Poincare Laplacian calculation. -/
  mixed_wirtinger_laplacian :
    N.PullbackMixedWirtingerLaplacianFormula
      upperHalfPlaneMap_contDiffOn affineMapDeriv_contDiffOn N.PullbackLogDensityTwiceDifferentiable
  /--
  The metric Schwarzian of the canonical pullback conformal factor is the
  ordinary branch Schwarzian.
  -/
  metricSchwarzian_eq_branchSchwarzian :
    N.PullbackMetricSchwarzianEqualsBranchSchwarzian
      upperHalfPlaneMap_contDiffOn affineMapDeriv_contDiffOn N.PullbackLogDensityTwiceDifferentiable
  /-- The derivative branch has the expected genuine derivative at the base point. -/
  affineMapDeriv_hasDerivAt_base :
    HasDerivAt (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z)
      (N.normalized.projective.affineMapSecondDeriv z₀) z₀
  /-- The upper-half-plane branch has the expected genuine derivative at the base point. -/
  upperHalfPlaneMap_hasDerivAt_base :
    HasDerivAt (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ))
      (N.normalized.projective.affineMapDeriv z₀) z₀

namespace LocalHyperbolicCanonicalPullbackMixedWirtingerLaplacianData

/--
The mixed-Wirtinger Laplacian package implies the canonical core package.

%%handwave
name:
  Core pullback data from the mixed Wirtinger Laplacian
statement:
  The identity $\partial_{\bar z}\partial_zv=\tfrac14\rho$ for the canonical pullback factor converts to $\Delta v=\rho$, yielding the core pullback package while retaining Schwarzian and base-derivative data.
-/
def toCoreData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (M : LocalHyperbolicCanonicalPullbackMixedWirtingerLaplacianData N) :
    LocalHyperbolicCanonicalPullbackCoreData N where
  upperHalfPlaneMap_contDiffOn := M.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := M.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := M.twice_differentiable_on_domain
  laplacian_eq_pullbackDensitySq :=
    N.laplacian_eq_pullbackDensitySq_of_mixedWirtingerLaplacianFormula
      M.mixed_wirtinger_laplacian
  metricSchwarzian_eq_branchSchwarzian := M.metricSchwarzian_eq_branchSchwarzian
  affineMapDeriv_hasDerivAt_base := M.affineMapDeriv_hasDerivAt_base
  upperHalfPlaneMap_hasDerivAt_base := M.upperHalfPlaneMap_hasDerivAt_base

end LocalHyperbolicCanonicalPullbackMixedWirtingerLaplacianData

/--
Core canonical pullback data with the mixed Laplacian identity reduced to the
`∂_{\bar z}` derivative of the explicit first Poincare pullback expression.
-/
structure LocalHyperbolicCanonicalPullbackMixedExpressionData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The upper-half-plane branch is `C^3` as a complex-valued function. -/
  upperHalfPlaneMap_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain
  /-- The derivative branch is `C^3` as a complex-valued function. -/
  affineMapDeriv_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain
  /-- The canonical pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : N.PullbackLogDensityTwiceDifferentiable
  /-- The explicit first Wirtinger derivative formula for the canonical pullback. -/
  first_wirtinger_formula :
    N.PullbackFirstWirtingerFormula
      upperHalfPlaneMap_contDiffOn affineMapDeriv_contDiffOn N.PullbackLogDensityTwiceDifferentiable
  /-- The mixed derivative calculation for the explicit first pullback expression. -/
  mixed_expression_derivative :
    N.PullbackMixedWirtingerExpressionDerivativeFormula
  /--
  The metric Schwarzian of the canonical pullback conformal factor is the
  ordinary branch Schwarzian.
  -/
  metricSchwarzian_eq_branchSchwarzian :
    N.PullbackMetricSchwarzianEqualsBranchSchwarzian
      upperHalfPlaneMap_contDiffOn affineMapDeriv_contDiffOn N.PullbackLogDensityTwiceDifferentiable
  /-- The derivative branch has the expected genuine derivative at the base point. -/
  affineMapDeriv_hasDerivAt_base :
    HasDerivAt (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z)
      (N.normalized.projective.affineMapSecondDeriv z₀) z₀
  /-- The upper-half-plane branch has the expected genuine derivative at the base point. -/
  upperHalfPlaneMap_hasDerivAt_base :
    HasDerivAt (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ))
      (N.normalized.projective.affineMapDeriv z₀) z₀

namespace LocalHyperbolicCanonicalPullbackMixedExpressionData

/--
The explicit mixed-expression package implies the mixed-Wirtinger Laplacian
package.

%%handwave
name:
  Mixed-Wirtinger Laplacian data from the explicit first expression
statement:
  The first Wirtinger formula for the pullback density and the antiholomorphic derivative of that expression combine to give the mixed-Wirtinger Laplacian identity.
-/
def toMixedWirtingerLaplacianData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (M : LocalHyperbolicCanonicalPullbackMixedExpressionData N) :
    LocalHyperbolicCanonicalPullbackMixedWirtingerLaplacianData N where
  upperHalfPlaneMap_contDiffOn := M.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := M.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := M.twice_differentiable_on_domain
  mixed_wirtinger_laplacian :=
    N.pullbackMixedWirtingerLaplacianFormula_of_firstWirtingerFormula_and_mixedExpressionDerivative
      M.first_wirtinger_formula M.mixed_expression_derivative
  metricSchwarzian_eq_branchSchwarzian := M.metricSchwarzian_eq_branchSchwarzian
  affineMapDeriv_hasDerivAt_base := M.affineMapDeriv_hasDerivAt_base
  upperHalfPlaneMap_hasDerivAt_base := M.upperHalfPlaneMap_hasDerivAt_base

/-- The explicit mixed-expression package implies the canonical core package.
%%handwave
name:
  Core pullback data from an explicit mixed expression
statement:
  The explicit first Wirtinger formula and its mixed derivative yield the Laplacian identity and hence the canonical core pullback data.
-/
def toCoreData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (M : LocalHyperbolicCanonicalPullbackMixedExpressionData N) :
    LocalHyperbolicCanonicalPullbackCoreData N :=
  M.toMixedWirtingerLaplacianData.toCoreData

end LocalHyperbolicCanonicalPullbackMixedExpressionData

/--
Canonical pullback data with the Schwarzian side reduced to the two explicit
Wirtinger formulas for
`v = (1 / 2) log (|F'|² / (Im F)²)`.

Lean proves separately that these two formulas imply the metric-Schwarzian
identity by algebra.  Thus this package is one step closer to the raw
quotient/logarithm derivative calculation.
-/
structure LocalHyperbolicCanonicalPullbackWirtingerFormulaData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The upper-half-plane branch is `C^3` as a complex-valued function. -/
  upperHalfPlaneMap_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain
  /-- The derivative branch is `C^3` as a complex-valued function. -/
  affineMapDeriv_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain
  /-- The canonical pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : N.PullbackLogDensityTwiceDifferentiable
  /-- The geometric Laplacian calculation for the Poincare pullback density. -/
  laplacian_eq_pullbackDensitySq :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian N.pullbackLogDensity z =
        N.pullbackDensitySq z
  /-- The explicit first Wirtinger derivative formula for the canonical pullback. -/
  first_wirtinger_formula :
    N.PullbackFirstWirtingerFormula
      upperHalfPlaneMap_contDiffOn affineMapDeriv_contDiffOn N.PullbackLogDensityTwiceDifferentiable
  /-- The explicit second Wirtinger derivative formula for the canonical pullback. -/
  second_wirtinger_formula :
    N.PullbackSecondWirtingerFormula
      upperHalfPlaneMap_contDiffOn affineMapDeriv_contDiffOn N.PullbackLogDensityTwiceDifferentiable
  /-- The derivative branch has the expected genuine derivative at the base point. -/
  affineMapDeriv_hasDerivAt_base :
    HasDerivAt (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z)
      (N.normalized.projective.affineMapSecondDeriv z₀) z₀
  /-- The upper-half-plane branch has the expected genuine derivative at the base point. -/
  upperHalfPlaneMap_hasDerivAt_base :
    HasDerivAt (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ))
      (N.normalized.projective.affineMapDeriv z₀) z₀

namespace LocalHyperbolicCanonicalPullbackWirtingerFormulaData

/--
The two explicit Wirtinger formulas imply the previous canonical pullback core
package.

%%handwave
name:
  Core pullback data from two Wirtinger formulas
statement:
  The explicit formulas for $v_z$ and $v_{zz}$ identify $2(v_{zz}-v_z^2)$ with the branch Schwarzian; together with the Laplacian and regularity data they yield the core package.
-/
def toCoreData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (W : LocalHyperbolicCanonicalPullbackWirtingerFormulaData N) :
    LocalHyperbolicCanonicalPullbackCoreData N where
  upperHalfPlaneMap_contDiffOn := W.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := W.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := W.twice_differentiable_on_domain
  laplacian_eq_pullbackDensitySq := W.laplacian_eq_pullbackDensitySq
  metricSchwarzian_eq_branchSchwarzian :=
    N.metricSchwarzian_eq_branchSchwarzian_of_wirtinger_formulas
      W.first_wirtinger_formula W.second_wirtinger_formula
  affineMapDeriv_hasDerivAt_base := W.affineMapDeriv_hasDerivAt_base
  upperHalfPlaneMap_hasDerivAt_base := W.upperHalfPlaneMap_hasDerivAt_base

/-- The explicit Wirtinger-formula package forgets to the canonical formula package.
%%handwave
name:
  Canonical Liouville formula from Wirtinger pullback data
statement:
  Forgetting the intermediate Wirtinger calculations retains the canonical pullback Liouville formula, its Laplacian equation, Schwarzian identity, and base one-jet.
-/
def toFormulaData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (W : LocalHyperbolicCanonicalPullbackWirtingerFormulaData N) :
    LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N :=
  W.toCoreData.toFormulaData

end LocalHyperbolicCanonicalPullbackWirtingerFormulaData

/--
Canonical pullback data with the first Wirtinger formula replaced by the
pointwise squared-density derivative formula.

The passage from `∂z ρ = ρ (...)` to the first logarithmic Wirtinger formula is
the Frechet-Wirtinger chain rule for `v = (1 / 2) log ρ`, already proved above.
The second Wirtinger formula remains explicit.
-/
structure LocalHyperbolicCanonicalPullbackDensityDerivativeData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The upper-half-plane branch is `C^3` as a complex-valued function. -/
  upperHalfPlaneMap_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain
  /-- The derivative branch is `C^3` as a complex-valued function. -/
  affineMapDeriv_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain
  /-- The canonical pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : N.PullbackLogDensityTwiceDifferentiable
  /-- The Poincare pullback squared density is real-differentiable pointwise. -/
  pullbackDensitySq_differentiableAt :
    ∀ z, z ∈ N.domain → DifferentiableAt ℝ N.pullbackDensitySq z
  /-- The pointwise first derivative formula for the Poincare pullback squared density. -/
  pullbackDensitySq_derivative :
    N.PullbackDensitySqDerivativeFormula
  /-- The geometric Laplacian calculation for the Poincare pullback density. -/
  laplacian_eq_pullbackDensitySq :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian N.pullbackLogDensity z =
        N.pullbackDensitySq z
  /-- The explicit second Wirtinger derivative formula for the canonical pullback. -/
  second_wirtinger_formula :
    N.PullbackSecondWirtingerFormula
      upperHalfPlaneMap_contDiffOn affineMapDeriv_contDiffOn N.PullbackLogDensityTwiceDifferentiable
  /-- The derivative branch has the expected genuine derivative at the base point. -/
  affineMapDeriv_hasDerivAt_base :
    HasDerivAt (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z)
      (N.normalized.projective.affineMapSecondDeriv z₀) z₀
  /-- The upper-half-plane branch has the expected genuine derivative at the base point. -/
  upperHalfPlaneMap_hasDerivAt_base :
    HasDerivAt (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ))
      (N.normalized.projective.affineMapDeriv z₀) z₀

namespace LocalHyperbolicCanonicalPullbackDensityDerivativeData

/--
The squared-density derivative package gives the explicit Wirtinger-formula
package.

%%handwave
name:
  Wirtinger pullback data from the squared-density derivative
statement:
  Differentiating $\rho=|F'|^2/(\operatorname{Im}F)^2$ and applying the logarithmic chain rule gives the first Wirtinger formula; together with the stored second formula this yields the Wirtinger package.
-/
def toWirtingerFormulaData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackDensityDerivativeData N) :
    LocalHyperbolicCanonicalPullbackWirtingerFormulaData N where
  upperHalfPlaneMap_contDiffOn := P.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := P.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := P.twice_differentiable_on_domain
  laplacian_eq_pullbackDensitySq := P.laplacian_eq_pullbackDensitySq
  first_wirtinger_formula :=
    N.pullbackFirstWirtingerFormula_of_densitySqDerivativeFormula
      P.pullbackDensitySq_differentiableAt P.pullbackDensitySq_derivative
  second_wirtinger_formula := P.second_wirtinger_formula
  affineMapDeriv_hasDerivAt_base := P.affineMapDeriv_hasDerivAt_base
  upperHalfPlaneMap_hasDerivAt_base := P.upperHalfPlaneMap_hasDerivAt_base

/-- The squared-density derivative package forgets to the canonical formula package.
%%handwave
name:
  Canonical Liouville formula from density-derivative data
statement:
  The derivative formula for the Poincaré pullback density yields the canonical logarithmic Wirtinger formula and hence the canonical Liouville formula package.
-/
def toFormulaData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackDensityDerivativeData N) :
    LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N :=
  P.toWirtingerFormulaData.toFormulaData

end LocalHyperbolicCanonicalPullbackDensityDerivativeData

/--
Canonical pullback data with the first-derivative side reduced to actual
complex derivatives of the branch and derivative branch.

From these derivative hypotheses Lean proves both differentiability of the
Poincare squared density and the pointwise squared-density derivative formula.
The remaining pullback-side analytic fields are then the Laplacian identity and
the second Wirtinger formula.
-/
structure LocalHyperbolicCanonicalPullbackBranchDerivativeData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The upper-half-plane branch is `C^3` as a complex-valued function. -/
  upperHalfPlaneMap_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain
  /-- The derivative branch is `C^3` as a complex-valued function. -/
  affineMapDeriv_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain
  /-- The canonical pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : N.PullbackLogDensityTwiceDifferentiable
  /-- The upper-half-plane branch has the expected actual derivative on the domain. -/
  upperHalfPlaneMap_hasDerivAt :
    ∀ z, z ∈ N.domain →
      HasDerivAt (fun w : ℂ ↦ (N.normalized.upperHalfPlaneMap w : ℂ))
        (N.normalized.projective.affineMapDeriv z) z
  /-- The derivative branch has the expected actual derivative on the domain. -/
  affineMapDeriv_hasDerivAt :
    ∀ z, z ∈ N.domain →
      HasDerivAt (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w)
        (N.normalized.projective.affineMapSecondDeriv z) z
  /-- The geometric Laplacian calculation for the Poincare pullback density. -/
  laplacian_eq_pullbackDensitySq :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian N.pullbackLogDensity z =
        N.pullbackDensitySq z
  /-- The explicit second Wirtinger derivative formula for the canonical pullback. -/
  second_wirtinger_formula :
    N.PullbackSecondWirtingerFormula
      upperHalfPlaneMap_contDiffOn affineMapDeriv_contDiffOn N.PullbackLogDensityTwiceDifferentiable

namespace LocalHyperbolicCanonicalPullbackBranchDerivativeData

/--
Actual branch derivative data imply the squared-density derivative package.

%%handwave
name:
  Density-derivative data from actual branch derivatives
statement:
  The identities $F'=F_1$ and $F_1'=F_2$ differentiate the Poincaré pullback density explicitly, producing its differentiability and derivative formula together with the remaining pullback data.
-/
def toDensityDerivativeData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (B : LocalHyperbolicCanonicalPullbackBranchDerivativeData N) :
    LocalHyperbolicCanonicalPullbackDensityDerivativeData N where
  upperHalfPlaneMap_contDiffOn := B.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := B.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := B.twice_differentiable_on_domain
  pullbackDensitySq_differentiableAt := by
    intro z hz
    exact N.pullbackDensitySq_differentiableAt_of_branch_hasDerivAt
      (B.upperHalfPlaneMap_hasDerivAt z hz) (B.affineMapDeriv_hasDerivAt z hz)
  pullbackDensitySq_derivative :=
    N.pullbackDensitySqDerivativeFormula_of_branch_hasDerivAt_on
      B.upperHalfPlaneMap_hasDerivAt B.affineMapDeriv_hasDerivAt
  laplacian_eq_pullbackDensitySq := B.laplacian_eq_pullbackDensitySq
  second_wirtinger_formula := B.second_wirtinger_formula
  affineMapDeriv_hasDerivAt_base := B.affineMapDeriv_hasDerivAt z₀ N.base_mem
  upperHalfPlaneMap_hasDerivAt_base := B.upperHalfPlaneMap_hasDerivAt z₀ N.base_mem

/-- Actual branch derivative data forget to the canonical formula package.
%%handwave
name:
  Canonical Liouville formula from branch derivative data
statement:
  Actual first and second branch derivatives imply the density derivative formula and therefore the canonical pullback Liouville formula.
-/
def toFormulaData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (B : LocalHyperbolicCanonicalPullbackBranchDerivativeData N) :
    LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N :=
  B.toDensityDerivativeData.toFormulaData

end LocalHyperbolicCanonicalPullbackBranchDerivativeData

/--
Canonical pullback data with the second Wirtinger formula reduced to the
Frechet derivative of the explicit first Wirtinger expression.

The first Wirtinger formula is still proved from the actual branch-derivative
fields via the squared-density calculation.  The only remaining
second-derivative pullback input here is the closed-form calculation
`∂z(first expression) = second expression`.
-/
structure LocalHyperbolicCanonicalPullbackSecondExpressionData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The upper-half-plane branch is `C^3` as a complex-valued function. -/
  upperHalfPlaneMap_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain
  /-- The derivative branch is `C^3` as a complex-valued function. -/
  affineMapDeriv_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain
  /-- The canonical pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : N.PullbackLogDensityTwiceDifferentiable
  /-- The upper-half-plane branch has the expected actual derivative on the domain. -/
  upperHalfPlaneMap_hasDerivAt :
    ∀ z, z ∈ N.domain →
      HasDerivAt (fun w : ℂ ↦ (N.normalized.upperHalfPlaneMap w : ℂ))
        (N.normalized.projective.affineMapDeriv z) z
  /-- The derivative branch has the expected actual derivative on the domain. -/
  affineMapDeriv_hasDerivAt :
    ∀ z, z ∈ N.domain →
      HasDerivAt (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w)
        (N.normalized.projective.affineMapSecondDeriv z) z
  /-- The geometric Laplacian calculation for the Poincare pullback density. -/
  laplacian_eq_pullbackDensitySq :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian N.pullbackLogDensity z =
        N.pullbackDensitySq z
  /--
  The explicit Frechet derivative formula for the first Wirtinger expression.
  -/
  second_expression_derivative :
    N.PullbackSecondWirtingerExpressionDerivativeFormula

namespace LocalHyperbolicCanonicalPullbackSecondExpressionData

/--
The explicit first-expression derivative package gives the actual branch
derivative package by the local-congruence bridge for Frechet derivatives.

%%handwave
name:
  Branch derivative data from the second Wirtinger expression
statement:
  The explicit derivative of the first pullback Wirtinger expression supplies the second Wirtinger formula, completing the package of actual branch derivatives and pullback identities.
-/
def toBranchDerivativeData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (E : LocalHyperbolicCanonicalPullbackSecondExpressionData N) :
    LocalHyperbolicCanonicalPullbackBranchDerivativeData N where
  upperHalfPlaneMap_contDiffOn := E.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := E.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := E.twice_differentiable_on_domain
  upperHalfPlaneMap_hasDerivAt := E.upperHalfPlaneMap_hasDerivAt
  affineMapDeriv_hasDerivAt := E.affineMapDeriv_hasDerivAt
  laplacian_eq_pullbackDensitySq := E.laplacian_eq_pullbackDensitySq
  second_wirtinger_formula := by
    have hDiff : ∀ z, z ∈ N.domain → DifferentiableAt ℝ N.pullbackDensitySq z := by
      intro z hz
      exact N.pullbackDensitySq_differentiableAt_of_branch_hasDerivAt
        (E.upperHalfPlaneMap_hasDerivAt z hz) (E.affineMapDeriv_hasDerivAt z hz)
    have hρ : N.PullbackDensitySqDerivativeFormula :=
      N.pullbackDensitySqDerivativeFormula_of_branch_hasDerivAt_on
        E.upperHalfPlaneMap_hasDerivAt E.affineMapDeriv_hasDerivAt
    have hZ :
        N.PullbackFirstWirtingerFormula
          E.upperHalfPlaneMap_contDiffOn E.affineMapDeriv_contDiffOn
          N.PullbackLogDensityTwiceDifferentiable :=
      N.pullbackFirstWirtingerFormula_of_densitySqDerivativeFormula hDiff hρ
    exact
      N.pullbackSecondWirtingerFormula_of_firstWirtingerFormula_and_expressionDerivative
        hZ E.second_expression_derivative

/-- The explicit first-expression derivative package forgets to the canonical formula package.
%%handwave
name:
  Canonical Liouville formula from the second-expression derivative
statement:
  The derivative formula for the explicit first Wirtinger expression implies the branch-derivative package and hence the canonical pullback Liouville formula.
-/
def toFormulaData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (E : LocalHyperbolicCanonicalPullbackSecondExpressionData N) :
    LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N :=
  E.toBranchDerivativeData.toFormulaData

end LocalHyperbolicCanonicalPullbackSecondExpressionData

/--
Canonical pullback data with the explicit second-expression derivative proved
from ordinary branch derivative identities through `F''`.

Compared with `LocalHyperbolicCanonicalPullbackSecondExpressionData`, this
replaces the closed-form Frechet derivative assumption by the actual identity
`d(F'') = F'''`.
-/
structure LocalHyperbolicCanonicalPullbackThirdDerivativeData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The upper-half-plane branch is `C^3` as a complex-valued function. -/
  upperHalfPlaneMap_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain
  /-- The derivative branch is `C^3` as a complex-valued function. -/
  affineMapDeriv_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain
  /-- The canonical pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : N.PullbackLogDensityTwiceDifferentiable
  /-- The upper-half-plane branch has the expected actual derivative on the domain. -/
  upperHalfPlaneMap_hasDerivAt :
    ∀ z, z ∈ N.domain →
      HasDerivAt (fun w : ℂ ↦ (N.normalized.upperHalfPlaneMap w : ℂ))
        (N.normalized.projective.affineMapDeriv z) z
  /-- The derivative branch has the expected actual derivative on the domain. -/
  affineMapDeriv_hasDerivAt :
    ∀ z, z ∈ N.domain →
      HasDerivAt (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w)
        (N.normalized.projective.affineMapSecondDeriv z) z
  /-- The second-derivative branch has the expected actual derivative on the domain. -/
  affineMapSecondDeriv_hasDerivAt :
    ∀ z, z ∈ N.domain →
      HasDerivAt (fun w : ℂ ↦ N.normalized.projective.affineMapSecondDeriv w)
        (N.normalized.projective.affineMapThirdDeriv z) z
  /-- The geometric Laplacian calculation for the Poincare pullback density. -/
  laplacian_eq_pullbackDensitySq :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian N.pullbackLogDensity z =
        N.pullbackDensitySq z

namespace LocalHyperbolicCanonicalPullbackThirdDerivativeData

/--
Ordinary branch derivatives through `F''` imply the explicit
second-expression derivative package.

%%handwave
name:
  Second-expression data from derivatives through third order
statement:
  The actual identities $F'=F_1$, $F_1'=F_2$, and $F_2'=F_3$ differentiate the explicit first Wirtinger expression and supply its prescribed second derivative formula.
-/
def toSecondExpressionData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (T : LocalHyperbolicCanonicalPullbackThirdDerivativeData N) :
    LocalHyperbolicCanonicalPullbackSecondExpressionData N where
  upperHalfPlaneMap_contDiffOn := T.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := T.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := T.twice_differentiable_on_domain
  upperHalfPlaneMap_hasDerivAt := T.upperHalfPlaneMap_hasDerivAt
  affineMapDeriv_hasDerivAt := T.affineMapDeriv_hasDerivAt
  laplacian_eq_pullbackDensitySq := T.laplacian_eq_pullbackDensitySq
  second_expression_derivative :=
    N.pullbackSecondWirtingerExpressionDerivativeFormula_of_branch_hasDerivAt_on
      T.upperHalfPlaneMap_hasDerivAt T.affineMapDeriv_hasDerivAt
      T.affineMapSecondDeriv_hasDerivAt

/-- The third-derivative package forgets to the canonical formula package.
%%handwave
name:
  Canonical Liouville formula from third-order branch data
statement:
  Actual branch derivatives through third order imply the explicit pullback Wirtinger identities and thus the canonical Liouville formula.
-/
def toFormulaData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (T : LocalHyperbolicCanonicalPullbackThirdDerivativeData N) :
    LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N :=
  T.toSecondExpressionData.toFormulaData

end LocalHyperbolicCanonicalPullbackThirdDerivativeData

/--
Canonical pullback data with the `ℍ`-valued derivative identification reduced
to the affine projective branch derivative.

The `ℍ`-valued branch agrees locally with the affine projective coordinate on
the open normalized domain, so Lean derives its actual derivative from the
affine one by local congruence.
-/
structure LocalHyperbolicCanonicalPullbackAffineDerivativeData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The upper-half-plane branch is `C^3` as a complex-valued function. -/
  upperHalfPlaneMap_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain
  /-- The derivative branch is `C^3` as a complex-valued function. -/
  affineMapDeriv_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain
  /-- The canonical pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : N.PullbackLogDensityTwiceDifferentiable
  /-- The affine projective branch has the expected actual derivative on the domain. -/
  affineMap_hasDerivAt :
    ∀ z, z ∈ N.domain →
      HasDerivAt N.normalized.projective.affineMap
        (N.normalized.projective.affineMapDeriv z) z
  /-- The derivative branch has the expected actual derivative on the domain. -/
  affineMapDeriv_hasDerivAt :
    ∀ z, z ∈ N.domain →
      HasDerivAt (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w)
        (N.normalized.projective.affineMapSecondDeriv z) z
  /-- The second-derivative branch has the expected actual derivative on the domain. -/
  affineMapSecondDeriv_hasDerivAt :
    ∀ z, z ∈ N.domain →
      HasDerivAt (fun w : ℂ ↦ N.normalized.projective.affineMapSecondDeriv w)
        (N.normalized.projective.affineMapThirdDeriv z) z
  /-- The geometric Laplacian calculation for the Poincare pullback density. -/
  laplacian_eq_pullbackDensitySq :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian N.pullbackLogDensity z =
        N.pullbackDensitySq z

namespace LocalHyperbolicCanonicalPullbackAffineDerivativeData

/--
Affine projective derivative data imply the third-derivative package for the
upper-half-plane branch.

%%handwave
name:
  Third-order upper-half-plane data from affine derivatives
statement:
  Because the normalized $\mathbb H$-valued branch agrees locally with its affine projective coordinate, actual affine derivatives through third order yield the corresponding upper-half-plane branch derivative package.
-/
def toThirdDerivativeData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackAffineDerivativeData N) :
    LocalHyperbolicCanonicalPullbackThirdDerivativeData N where
  upperHalfPlaneMap_contDiffOn := A.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := A.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := A.twice_differentiable_on_domain
  upperHalfPlaneMap_hasDerivAt :=
    N.upperHalfPlaneMap_hasDerivAt_of_affineMap_hasDerivAt_on
      A.affineMap_hasDerivAt
  affineMapDeriv_hasDerivAt := A.affineMapDeriv_hasDerivAt
  affineMapSecondDeriv_hasDerivAt := A.affineMapSecondDeriv_hasDerivAt
  laplacian_eq_pullbackDensitySq := A.laplacian_eq_pullbackDensitySq

/-- The affine-derivative package forgets to the canonical formula package.
%%handwave
name:
  Canonical Liouville formula from affine derivative data
statement:
  Actual affine projective derivatives through third order, together with the pullback Laplacian identity, determine the canonical pullback Liouville formula.
-/
def toFormulaData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackAffineDerivativeData N) :
    LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N :=
  A.toThirdDerivativeData.toFormulaData

end LocalHyperbolicCanonicalPullbackAffineDerivativeData

/--
Affine derivative algebra for the canonical Poincare pullback, separated from
the geometric Laplacian identity.

This is the same actual `HasDerivAt` branch information as
`LocalHyperbolicCanonicalPullbackAffineDerivativeData`, but without the
remaining curvature/Laplacian calculation.
-/
structure LocalHyperbolicCanonicalPullbackAffineDerivativeAlgebraData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The upper-half-plane branch is `C^3` as a complex-valued function. -/
  upperHalfPlaneMap_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain
  /-- The derivative branch is `C^3` as a complex-valued function. -/
  affineMapDeriv_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain
  /-- The canonical pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : N.PullbackLogDensityTwiceDifferentiable
  /-- The affine projective branch has the expected actual derivative on the domain. -/
  affineMap_hasDerivAt :
    ∀ z, z ∈ N.domain →
      HasDerivAt N.normalized.projective.affineMap
        (N.normalized.projective.affineMapDeriv z) z
  /-- The derivative branch has the expected actual derivative on the domain. -/
  affineMapDeriv_hasDerivAt :
    ∀ z, z ∈ N.domain →
      HasDerivAt (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w)
        (N.normalized.projective.affineMapSecondDeriv z) z
  /-- The second-derivative branch has the expected actual derivative on the domain. -/
  affineMapSecondDeriv_hasDerivAt :
    ∀ z, z ∈ N.domain →
      HasDerivAt (fun w : ℂ ↦ N.normalized.projective.affineMapSecondDeriv w)
        (N.normalized.projective.affineMapThirdDeriv z) z

namespace LocalHyperbolicCanonicalPullbackAffineDerivativeAlgebraData

/--
Actual affine derivative algebra gives the explicit mixed-expression pullback
package, including the Poincare mixed derivative calculation.

%%handwave
name:
  Mixed pullback expressions from affine derivative algebra
statement:
  Actual affine derivatives through third order imply the first pullback Wirtinger formula, its mixed derivative, the Poincaré mixed-Laplacian identity, and the metric-Schwarzian identity.
-/
def toMixedExpressionData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackAffineDerivativeAlgebraData N) :
    LocalHyperbolicCanonicalPullbackMixedExpressionData N where
  upperHalfPlaneMap_contDiffOn := A.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := A.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := A.twice_differentiable_on_domain
  first_wirtinger_formula := by
    have hUpper :
        ∀ z, z ∈ N.domain →
          HasDerivAt (fun w : ℂ ↦ (N.normalized.upperHalfPlaneMap w : ℂ))
            (N.normalized.projective.affineMapDeriv z) z :=
      N.upperHalfPlaneMap_hasDerivAt_of_affineMap_hasDerivAt_on
        A.affineMap_hasDerivAt
    have hDiff : ∀ z, z ∈ N.domain → DifferentiableAt ℝ N.pullbackDensitySq z := by
      intro z hz
      exact N.pullbackDensitySq_differentiableAt_of_branch_hasDerivAt
        (hUpper z hz) (A.affineMapDeriv_hasDerivAt z hz)
    have hρ : N.PullbackDensitySqDerivativeFormula :=
      N.pullbackDensitySqDerivativeFormula_of_branch_hasDerivAt_on
        hUpper A.affineMapDeriv_hasDerivAt
    exact N.pullbackFirstWirtingerFormula_of_densitySqDerivativeFormula hDiff hρ
  mixed_expression_derivative := by
    exact N.pullbackMixedWirtingerExpressionDerivativeFormula_of_branch_hasDerivAt_on
      (N.upperHalfPlaneMap_hasDerivAt_of_affineMap_hasDerivAt_on
        A.affineMap_hasDerivAt)
      A.affineMapDeriv_hasDerivAt
      A.affineMapSecondDeriv_hasDerivAt
  metricSchwarzian_eq_branchSchwarzian := by
    have hUpper :
        ∀ z, z ∈ N.domain →
          HasDerivAt (fun w : ℂ ↦ (N.normalized.upperHalfPlaneMap w : ℂ))
            (N.normalized.projective.affineMapDeriv z) z :=
      N.upperHalfPlaneMap_hasDerivAt_of_affineMap_hasDerivAt_on
        A.affineMap_hasDerivAt
    have hDiff : ∀ z, z ∈ N.domain → DifferentiableAt ℝ N.pullbackDensitySq z := by
      intro z hz
      exact N.pullbackDensitySq_differentiableAt_of_branch_hasDerivAt
        (hUpper z hz) (A.affineMapDeriv_hasDerivAt z hz)
    have hρ : N.PullbackDensitySqDerivativeFormula :=
      N.pullbackDensitySqDerivativeFormula_of_branch_hasDerivAt_on
        hUpper A.affineMapDeriv_hasDerivAt
    have hZ :
        N.PullbackFirstWirtingerFormula
          A.upperHalfPlaneMap_contDiffOn A.affineMapDeriv_contDiffOn
          N.PullbackLogDensityTwiceDifferentiable :=
      N.pullbackFirstWirtingerFormula_of_densitySqDerivativeFormula hDiff hρ
    have hExpr : N.PullbackSecondWirtingerExpressionDerivativeFormula :=
      N.pullbackSecondWirtingerExpressionDerivativeFormula_of_branch_hasDerivAt_on
        hUpper A.affineMapDeriv_hasDerivAt A.affineMapSecondDeriv_hasDerivAt
    have hZZ :
        N.PullbackSecondWirtingerFormula
          A.upperHalfPlaneMap_contDiffOn A.affineMapDeriv_contDiffOn
          N.PullbackLogDensityTwiceDifferentiable :=
      N.pullbackSecondWirtingerFormula_of_firstWirtingerFormula_and_expressionDerivative
        hZ hExpr
    exact N.metricSchwarzian_eq_branchSchwarzian_of_wirtinger_formulas hZ hZZ
  affineMapDeriv_hasDerivAt_base := A.affineMapDeriv_hasDerivAt z₀ N.base_mem
  upperHalfPlaneMap_hasDerivAt_base :=
    (N.upperHalfPlaneMap_hasDerivAt_of_affineMap_hasDerivAt_on
      A.affineMap_hasDerivAt) z₀ N.base_mem

/-- Actual affine derivative algebra gives the canonical core pullback package.
%%handwave
name:
  Core pullback data from affine derivative algebra
statement:
  The derivative algebra of the normalized affine branch yields both the Poincaré pullback Laplacian calculation and the metric-Schwarzian compatibility required by the core package.
-/
def toCoreData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackAffineDerivativeAlgebraData N) :
    LocalHyperbolicCanonicalPullbackCoreData N :=
  A.toMixedExpressionData.toCoreData

/-- Add the geometric Poincare Laplacian identity to the affine derivative algebra package.
%%handwave
name:
  Affine derivative data with the Poincaré Laplacian identity
statement:
  Adjoin $\Delta v=|F'|^2/(\operatorname{Im}F)^2$ to the regular affine derivative algebra to obtain the full affine pullback data.
-/
def withLaplacian
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackAffineDerivativeAlgebraData N)
    (hlap :
      ∀ z, z ∈ N.domain →
        Laplacian.laplacian N.pullbackLogDensity z =
          N.pullbackDensitySq z) :
    LocalHyperbolicCanonicalPullbackAffineDerivativeData N where
  upperHalfPlaneMap_contDiffOn := A.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := A.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := A.twice_differentiable_on_domain
  affineMap_hasDerivAt := A.affineMap_hasDerivAt
  affineMapDeriv_hasDerivAt := A.affineMapDeriv_hasDerivAt
  affineMapSecondDeriv_hasDerivAt := A.affineMapSecondDeriv_hasDerivAt
  laplacian_eq_pullbackDensitySq := hlap

end LocalHyperbolicCanonicalPullbackAffineDerivativeAlgebraData

namespace LocalHyperbolicCanonicalPullbackAffineDerivativeData

end LocalHyperbolicCanonicalPullbackAffineDerivativeData

/--
Regularity part of the canonical pullback derivative-algebra package.

This keeps the smoothness and curvature-regularity assumptions separate from
the algebraic derivative identifications for the affine branch.
-/
structure LocalHyperbolicCanonicalPullbackRegularityData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The upper-half-plane branch is `C^3` as a complex-valued function. -/
  upperHalfPlaneMap_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain
  /-- The derivative branch is `C^3` as a complex-valued function. -/
  affineMapDeriv_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain
  /-- The canonical pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : N.PullbackLogDensityTwiceDifferentiable




/--
Derivative-identification part of the canonical pullback derivative-algebra
package.

These fields say that the symbolic branches carried by the local projective
map are the actual complex derivatives seen by mathlib.
-/
structure LocalHyperbolicCanonicalPullbackDerivativeIdentificationData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The affine projective branch is complex differentiable on the domain. -/
  affineMap_differentiableAt :
    ∀ z, z ∈ N.domain →
      DifferentiableAt ℂ N.normalized.projective.affineMap z
  /-- The symbolic first derivative is mathlib's complex derivative. -/
  affineMap_deriv_eq :
    ∀ z, z ∈ N.domain →
      deriv N.normalized.projective.affineMap z =
        N.normalized.projective.affineMapDeriv z
  /-- The symbolic first-derivative branch is complex differentiable on the domain. -/
  affineMapDeriv_differentiableAt :
    ∀ z, z ∈ N.domain →
      DifferentiableAt ℂ
        (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w) z
  /-- The symbolic second derivative is mathlib's derivative of the first derivative. -/
  affineMapDeriv_deriv_eq :
    ∀ z, z ∈ N.domain →
      deriv (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w) z =
        N.normalized.projective.affineMapSecondDeriv z
  /-- The symbolic second-derivative branch is complex differentiable on the domain. -/
  affineMapSecondDeriv_differentiableAt :
    ∀ z, z ∈ N.domain →
      DifferentiableAt ℂ
        (fun w : ℂ ↦ N.normalized.projective.affineMapSecondDeriv w) z
  /-- The symbolic third derivative is mathlib's derivative of the second derivative. -/
  affineMapSecondDeriv_deriv_eq :
    ∀ z, z ∈ N.domain →
      deriv (fun w : ℂ ↦ N.normalized.projective.affineMapSecondDeriv w) z =
        N.normalized.projective.affineMapThirdDeriv z


namespace LocalHyperbolicCanonicalPullbackDerivativeIdentificationData

end LocalHyperbolicCanonicalPullbackDerivativeIdentificationData

/--
Canonical pullback data with affine derivative hypotheses phrased through
mathlib's `deriv` operator.

The actual `HasDerivAt` statements used by the Wirtinger calculations are
derived from complex differentiability and the displayed derivative
identifications.
-/
structure LocalHyperbolicCanonicalPullbackDerivativeAlgebraData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The upper-half-plane branch is `C^3` as a complex-valued function. -/
  upperHalfPlaneMap_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain
  /-- The derivative branch is `C^3` as a complex-valued function. -/
  affineMapDeriv_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain
  /-- The canonical pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : N.PullbackLogDensityTwiceDifferentiable
  /-- The affine projective branch is complex differentiable on the domain. -/
  affineMap_differentiableAt :
    ∀ z, z ∈ N.domain →
      DifferentiableAt ℂ N.normalized.projective.affineMap z
  /-- The symbolic first derivative is mathlib's complex derivative. -/
  affineMap_deriv_eq :
    ∀ z, z ∈ N.domain →
      deriv N.normalized.projective.affineMap z =
        N.normalized.projective.affineMapDeriv z
  /-- The symbolic first-derivative branch is complex differentiable on the domain. -/
  affineMapDeriv_differentiableAt :
    ∀ z, z ∈ N.domain →
      DifferentiableAt ℂ
        (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w) z
  /-- The symbolic second derivative is mathlib's derivative of the first derivative. -/
  affineMapDeriv_deriv_eq :
    ∀ z, z ∈ N.domain →
      deriv (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w) z =
        N.normalized.projective.affineMapSecondDeriv z
  /-- The symbolic second-derivative branch is complex differentiable on the domain. -/
  affineMapSecondDeriv_differentiableAt :
    ∀ z, z ∈ N.domain →
      DifferentiableAt ℂ
        (fun w : ℂ ↦ N.normalized.projective.affineMapSecondDeriv w) z
  /-- The symbolic third derivative is mathlib's derivative of the second derivative. -/
  affineMapSecondDeriv_deriv_eq :
    ∀ z, z ∈ N.domain →
      deriv (fun w : ℂ ↦ N.normalized.projective.affineMapSecondDeriv w) z =
        N.normalized.projective.affineMapThirdDeriv z

namespace LocalHyperbolicCanonicalPullbackRegularityData

/-- Combine regularity data with derivative identifications.
%%handwave
name:
  Pullback derivative algebra from regularity and identifications
statement:
  Smoothness of the normalized branch and pullback density, combined with identifications of the first three symbolic derivatives as actual derivatives, forms the canonical derivative-algebra package.
-/
def withDerivativeIdentification
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (R : LocalHyperbolicCanonicalPullbackRegularityData N)
    (I : LocalHyperbolicCanonicalPullbackDerivativeIdentificationData N) :
    LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N where
  upperHalfPlaneMap_contDiffOn := R.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := R.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := R.twice_differentiable_on_domain
  affineMap_differentiableAt := I.affineMap_differentiableAt
  affineMap_deriv_eq := I.affineMap_deriv_eq
  affineMapDeriv_differentiableAt := I.affineMapDeriv_differentiableAt
  affineMapDeriv_deriv_eq := I.affineMapDeriv_deriv_eq
  affineMapSecondDeriv_differentiableAt := I.affineMapSecondDeriv_differentiableAt
  affineMapSecondDeriv_deriv_eq := I.affineMapSecondDeriv_deriv_eq

end LocalHyperbolicCanonicalPullbackRegularityData

/--
Canonical pullback data with derivative algebra separated from the geometric
Laplacian identity.
-/
structure LocalHyperbolicCanonicalPullbackDerivIdentifiedData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The upper-half-plane branch is `C^3` as a complex-valued function. -/
  upperHalfPlaneMap_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ (N.normalized.upperHalfPlaneMap z : ℂ)) N.domain
  /-- The derivative branch is `C^3` as a complex-valued function. -/
  affineMapDeriv_contDiffOn :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ N.normalized.projective.affineMapDeriv z) N.domain
  /-- The canonical pullback logarithmic density has enough regularity for curvature. -/
  twice_differentiable_on_domain : N.PullbackLogDensityTwiceDifferentiable
  /-- The affine projective branch is complex differentiable on the domain. -/
  affineMap_differentiableAt :
    ∀ z, z ∈ N.domain →
      DifferentiableAt ℂ N.normalized.projective.affineMap z
  /-- The symbolic first derivative is mathlib's complex derivative. -/
  affineMap_deriv_eq :
    ∀ z, z ∈ N.domain →
      deriv N.normalized.projective.affineMap z =
        N.normalized.projective.affineMapDeriv z
  /-- The symbolic first-derivative branch is complex differentiable on the domain. -/
  affineMapDeriv_differentiableAt :
    ∀ z, z ∈ N.domain →
      DifferentiableAt ℂ
        (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w) z
  /-- The symbolic second derivative is mathlib's derivative of the first derivative. -/
  affineMapDeriv_deriv_eq :
    ∀ z, z ∈ N.domain →
      deriv (fun w : ℂ ↦ N.normalized.projective.affineMapDeriv w) z =
        N.normalized.projective.affineMapSecondDeriv z
  /-- The symbolic second-derivative branch is complex differentiable on the domain. -/
  affineMapSecondDeriv_differentiableAt :
    ∀ z, z ∈ N.domain →
      DifferentiableAt ℂ
        (fun w : ℂ ↦ N.normalized.projective.affineMapSecondDeriv w) z
  /-- The symbolic third derivative is mathlib's derivative of the second derivative. -/
  affineMapSecondDeriv_deriv_eq :
    ∀ z, z ∈ N.domain →
      deriv (fun w : ℂ ↦ N.normalized.projective.affineMapSecondDeriv w) z =
        N.normalized.projective.affineMapThirdDeriv z
  /-- The geometric Laplacian calculation for the Poincare pullback density. -/
  laplacian_eq_pullbackDensitySq :
    ∀ z, z ∈ N.domain →
      Laplacian.laplacian N.pullbackLogDensity z =
        N.pullbackDensitySq z

namespace LocalHyperbolicCanonicalPullbackDerivativeAlgebraData

/-- Add the geometric Laplacian calculation to the derivative algebra package.
%%handwave
name:
  Derivative-identified pullback data with the Laplacian
statement:
  Adjoining the Poincaré identity $\Delta v=\rho$ to canonical derivative algebra yields pullback data containing both derivative identifications and curvature.
-/
def withLaplacian
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N)
    (hlap :
      ∀ z, z ∈ N.domain →
        Laplacian.laplacian N.pullbackLogDensity z =
          N.pullbackDensitySq z) :
    LocalHyperbolicCanonicalPullbackDerivIdentifiedData N where
  upperHalfPlaneMap_contDiffOn := A.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := A.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := A.twice_differentiable_on_domain
  affineMap_differentiableAt := A.affineMap_differentiableAt
  affineMap_deriv_eq := A.affineMap_deriv_eq
  affineMapDeriv_differentiableAt := A.affineMapDeriv_differentiableAt
  affineMapDeriv_deriv_eq := A.affineMapDeriv_deriv_eq
  affineMapSecondDeriv_differentiableAt := A.affineMapSecondDeriv_differentiableAt
  affineMapSecondDeriv_deriv_eq := A.affineMapSecondDeriv_deriv_eq
  laplacian_eq_pullbackDensitySq := hlap

/--
Derivative algebra also gives actual affine `HasDerivAt` algebra: mathlib
turns differentiability plus the stored `deriv` equality into the expected
complex derivative statements.

%%handwave
name:
  Actual affine derivatives from derivative identifications
statement:
  Complex differentiability together with the identities $f'=f_1$, $f_1'=f_2$, and $f_2'=f_3$ yields the corresponding actual derivative statements for the affine branch.
-/
def toAffineDerivativeAlgebraData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N) :
    LocalHyperbolicCanonicalPullbackAffineDerivativeAlgebraData N where
  upperHalfPlaneMap_contDiffOn := A.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := A.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := A.twice_differentiable_on_domain
  affineMap_hasDerivAt := by
    intro z hz
    exact
      LocalHyperbolicTwoJetUpperHalfPlaneNormalization.hasDerivAt_of_differentiableAt_deriv_eq
        (A.affineMap_differentiableAt z hz)
        (A.affineMap_deriv_eq z hz)
  affineMapDeriv_hasDerivAt := by
    intro z hz
    exact
      LocalHyperbolicTwoJetUpperHalfPlaneNormalization.hasDerivAt_of_differentiableAt_deriv_eq
        (A.affineMapDeriv_differentiableAt z hz)
        (A.affineMapDeriv_deriv_eq z hz)
  affineMapSecondDeriv_hasDerivAt := by
    intro z hz
    exact
      LocalHyperbolicTwoJetUpperHalfPlaneNormalization.hasDerivAt_of_differentiableAt_deriv_eq
        (A.affineMapSecondDeriv_differentiableAt z hz)
        (A.affineMapSecondDeriv_deriv_eq z hz)

end LocalHyperbolicCanonicalPullbackDerivativeAlgebraData

namespace LocalHyperbolicCanonicalPullbackDerivIdentifiedData

/--
Derivative identifications through mathlib's `deriv` imply the affine
`HasDerivAt` package.

%%handwave
name:
  Affine derivative data from identified symbolic derivatives
statement:
  The canonical differentiability and derivative equalities through third order convert to actual affine derivative statements, while retaining the Poincaré Laplacian identity.
-/
def toAffineDerivativeData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackDerivIdentifiedData N) :
    LocalHyperbolicCanonicalPullbackAffineDerivativeData N where
  upperHalfPlaneMap_contDiffOn := A.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := A.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := A.twice_differentiable_on_domain
  affineMap_hasDerivAt := by
    intro z hz
    exact
      LocalHyperbolicTwoJetUpperHalfPlaneNormalization.hasDerivAt_of_differentiableAt_deriv_eq
      (A.affineMap_differentiableAt z hz) (A.affineMap_deriv_eq z hz)
  affineMapDeriv_hasDerivAt := by
    intro z hz
    exact
      LocalHyperbolicTwoJetUpperHalfPlaneNormalization.hasDerivAt_of_differentiableAt_deriv_eq
      (A.affineMapDeriv_differentiableAt z hz)
      (A.affineMapDeriv_deriv_eq z hz)
  affineMapSecondDeriv_hasDerivAt := by
    intro z hz
    exact
      LocalHyperbolicTwoJetUpperHalfPlaneNormalization.hasDerivAt_of_differentiableAt_deriv_eq
      (A.affineMapSecondDeriv_differentiableAt z hz)
      (A.affineMapSecondDeriv_deriv_eq z hz)
  laplacian_eq_pullbackDensitySq := A.laplacian_eq_pullbackDensitySq

/-- The deriv-identified package forgets to the canonical formula package.
%%handwave
name:
  Canonical Liouville formula from identified derivatives
statement:
  Identified first three derivatives and the pullback Laplacian identity imply the affine package and therefore the canonical Liouville formula.
-/
def toFormulaData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackDerivIdentifiedData N) :
    LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N :=
  A.toAffineDerivativeData.toFormulaData

end LocalHyperbolicCanonicalPullbackDerivIdentifiedData

namespace LocalHyperbolicCanonicalPullbackAffineDerivativeAlgebraData

end LocalHyperbolicCanonicalPullbackAffineDerivativeAlgebraData

namespace LocalHyperbolicCanonicalPullbackAffineDerivativeData

/--
Actual affine `HasDerivAt` statements imply the derivative-identification
package phrased with mathlib's `deriv`.

%%handwave
name:
  Derivative identifications from actual affine derivatives
statement:
  Actual derivative statements for the affine branch and its first two derivatives imply complex differentiability and the equalities of the symbolic derivative fields with ordinary complex derivatives.
-/
def toDerivativeIdentificationData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackAffineDerivativeData N) :
    LocalHyperbolicCanonicalPullbackDerivativeIdentificationData N where
  affineMap_differentiableAt := by
    intro z hz
    exact (A.affineMap_hasDerivAt z hz).differentiableAt
  affineMap_deriv_eq := by
    intro z hz
    exact (A.affineMap_hasDerivAt z hz).deriv
  affineMapDeriv_differentiableAt := by
    intro z hz
    exact (A.affineMapDeriv_hasDerivAt z hz).differentiableAt
  affineMapDeriv_deriv_eq := by
    intro z hz
    exact (A.affineMapDeriv_hasDerivAt z hz).deriv
  affineMapSecondDeriv_differentiableAt := by
    intro z hz
    exact (A.affineMapSecondDeriv_hasDerivAt z hz).differentiableAt
  affineMapSecondDeriv_deriv_eq := by
    intro z hz
    exact (A.affineMapSecondDeriv_hasDerivAt z hz).deriv

/-- Actual affine derivative data forget to the regularity package.
%%handwave
name:
  Pullback regularity underlying affine derivative data
statement:
  Forgetting derivative identities from the full affine package retains $C^3$ branch regularity and the curvature regularity of the pullback logarithmic density.
-/
def toRegularityData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackAffineDerivativeData N) :
    LocalHyperbolicCanonicalPullbackRegularityData N where
  upperHalfPlaneMap_contDiffOn := A.upperHalfPlaneMap_contDiffOn
  affineMapDeriv_contDiffOn := A.affineMapDeriv_contDiffOn
  twice_differentiable_on_domain := A.twice_differentiable_on_domain

/-- Actual affine derivative data give the derivative-algebra package.
%%handwave
name:
  Canonical derivative algebra from actual affine derivatives
statement:
  Combine the regularity of the pullback construction with the derivative identifications obtained from actual affine derivatives through third order.
-/
def toDerivativeAlgebraData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackAffineDerivativeData N) :
    LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N :=
  A.toRegularityData.withDerivativeIdentification A.toDerivativeIdentificationData

/--
Actual affine derivative data also give the derivative-identified package,
because this older package already includes the Poincare Laplacian field.

%%handwave
name:
  Derivative-identified pullback package from affine data
statement:
  Actual affine derivatives yield canonical derivative algebra, and adjoining the stored Poincaré Laplacian identity gives the derivative-identified pullback package.
-/
def toDerivIdentifiedData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackAffineDerivativeData N) :
    LocalHyperbolicCanonicalPullbackDerivIdentifiedData N :=
  A.toDerivativeAlgebraData.withLaplacian A.laplacian_eq_pullbackDensitySq

end LocalHyperbolicCanonicalPullbackAffineDerivativeData

/--
The Liouville solution obtained from the Poincare pullback of a two-jet
normalized upper-half-plane branch.

Analytically, if `F : U → ℍ` is the normalized branch, this conformal factor is
`v = log |F'| - log Im(F)`, so
`exp(2v) = |F'|² / (Im F)²`.  The structure keeps that pullback formula
explicit and records the two pieces needed for uniqueness against the original
metric factor `u`: the same Schwarzian coefficient and the same normalized base
data.
-/
structure LocalHyperbolicPullbackLiouvilleCandidate
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀) where
  /-- The conformal factor induced by the Poincare pullback of the normalized branch. -/
  conformalFactor : LocalConformalFactor
  /-- Its coordinate domain is exactly the normalized branch domain. -/
  coordinateDomain_eq : conformalFactor.coordinateDomain = N.domain
  /-- The Poincare pullback factor solves the hyperbolic Liouville equation. -/
  solvesLiouville : conformalFactor.SolvesLiouvilleEquation
  /-- Its squared density is the Poincare pullback squared density. -/
  densitySq_eq_pullback :
    ∀ z, z ∈ N.domain →
      conformalFactor.densitySq z =
        Complex.normSq (N.normalized.projective.affineMapDeriv z) /
          ((N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2)
  /--
  The Schwarzian coefficient computed from this Liouville factor agrees with
  the original coefficient `S.coefficient` on the local domain.
  -/
  same_schwarzian_coefficient :
    ∀ z, z ∈ N.domain →
      LocalSchwarzianData.metricSchwarzianCoefficient
          conformalFactor.halfSchwarzianCoefficient z =
        S.coefficient z
  /-- The base point lies in the pullback domain. -/
  base_mem : z₀ ∈ N.domain
  /-- The two factors have the same squared density at the base point. -/
  base_densitySq_eq :
    conformalFactor.densitySq z₀ = u.densitySq z₀
  /--
  The first Wirtinger derivative of the pullback log-density agrees with the
  canonical derivative of the original conformal factor at the base point.
  -/
  base_uZ_eq :
    conformalFactor.wirtingerZ z₀ = u.wirtingerZ z₀

namespace LocalHyperbolicPullbackLiouvilleCandidate

/-- Package explicit pullback formula data as a pullback Liouville candidate.
%%handwave
name:
  Pullback Liouville candidate from explicit formula data
statement:
  Explicit pullback formula data define a competing Liouville factor on the normalized branch domain with the same pullback density, Schwarzian coefficient, base density, and base Wirtinger derivative as the original factor.
-/
def ofFormulaData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicPullbackLiouvilleFormulaData N) :
    LocalHyperbolicPullbackLiouvilleCandidate N where
  conformalFactor := P.conformalFactor
  coordinateDomain_eq := rfl
  solvesLiouville := P.solvesLiouville
  densitySq_eq_pullback := by
    intro z hz
    simpa [LocalHyperbolicPullbackLiouvilleFormulaData.conformalFactor,
      LocalConformalFactor.densitySq] using P.densitySq_eq_pullback z hz
  same_schwarzian_coefficient := P.same_schwarzian_coefficient
  base_mem := N.base_mem
  base_densitySq_eq := by
    simpa [LocalHyperbolicPullbackLiouvilleFormulaData.conformalFactor,
      LocalConformalFactor.densitySq] using P.base_densitySq_eq
  base_uZ_eq := P.conformalFactor_wirtingerZ_base_eq

/--
%%handwave
name: Schwarzian coefficient of the canonical pullback candidate
statement:
  Let $S$ be a prescribed Schwarzian coefficient on $\Omega$ and let $v$ be the canonical Poincare pullback logarithmic density packaged as a Liouville candidate. Then the metric Schwarzian of $v$ equals $S(z)$ for every $z\in\Omega$.
proof:
  Unpack the candidate and apply the Schwarzian compatibility of the canonical pullback formula.
-/
theorem ofCanonicalFormulaData_metricSchwarzian_eq_coefficient
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N) :
    ∀ z, z ∈ N.domain →
      LocalSchwarzianData.metricSchwarzianCoefficient
        (LocalHyperbolicPullbackLiouvilleCandidate.ofFormulaData
          P.toFormulaData).conformalFactor.halfSchwarzianCoefficient z =
      S.coefficient z := by
  intro z hz
  simpa [LocalHyperbolicPullbackLiouvilleCandidate.ofFormulaData] using
    P.toFormulaData_metricSchwarzian_eq_coefficient z hz

/--
%%handwave
name: Equality of the original and pullback metric Schwarzians
statement:
  Let $u$ be a local conformal factor and $v$ its canonical Poincare pullback candidate on $\Omega$. If a coefficient $S$ equals the metric Schwarzian of $u$ on $\Omega$ and the metric Schwarzian of $v$ equals $S$, then the metric Schwarzians of $u$ and $v$ agree pointwise on $\Omega$.
proof:
  At each point, identify the metric Schwarzian of $v$ with $S$ and then use the assumed identification of $S$ with the metric Schwarzian of $u$.
-/
theorem ofCanonicalFormulaData_same_metricSchwarzian_of_original
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N)
    (hOriginal :
      ∀ z, z ∈ N.domain →
        S.coefficient z =
          LocalSchwarzianData.metricSchwarzianCoefficient
            u.halfSchwarzianCoefficient z) :
    ∀ z, z ∈ N.domain →
      LocalSchwarzianData.metricSchwarzianCoefficient
        (LocalHyperbolicPullbackLiouvilleCandidate.ofFormulaData
          P.toFormulaData).conformalFactor.halfSchwarzianCoefficient z =
      LocalSchwarzianData.metricSchwarzianCoefficient
        u.halfSchwarzianCoefficient z := by
  intro z hz
  calc
    LocalSchwarzianData.metricSchwarzianCoefficient
        (LocalHyperbolicPullbackLiouvilleCandidate.ofFormulaData
          P.toFormulaData).conformalFactor.halfSchwarzianCoefficient z =
        S.coefficient z :=
          ofCanonicalFormulaData_metricSchwarzian_eq_coefficient P z hz
    _ = LocalSchwarzianData.metricSchwarzianCoefficient
        u.halfSchwarzianCoefficient z := hOriginal z hz

/--
%%handwave
name: Equal logarithmic densities give equal squared densities
statement:
  If two conformal logarithmic densities satisfy $u(z)=v(z)$ at a point $z$, then their squared densities satisfy $e^{2u(z)}=e^{2v(z)}$.
proof:
  Substitute the equality into the definition of squared conformal density.
-/
theorem densitySq_eq_of_logDensity_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    {z : ℂ}
    (hEq : u.logDensity z = C.conformalFactor.logDensity z) :
    u.densitySq z = C.conformalFactor.densitySq z := by
  simp [LocalConformalFactor.densitySq, hEq]

/--
%%handwave
name: Equal positive squared densities give equal logarithmic densities
statement:
  If two conformal factors have equal squared densities at $z_0$, then their logarithmic densities agree at $z_0$.
proof:
  The hypothesis is $e^{2v(z_0)}=e^{2u(z_0)}$. Injectivity of the real exponential gives $2v(z_0)=2u(z_0)$, and cancellation of $2$ yields the claim.
-/
theorem base_logDensity_eq
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (C : LocalHyperbolicPullbackLiouvilleCandidate N) :
    C.conformalFactor.logDensity z₀ = u.logDensity z₀ := by
  have hExp :
      Real.exp (2 * C.conformalFactor.logDensity z₀) =
        Real.exp (2 * u.logDensity z₀) := by
    simpa [LocalConformalFactor.densitySq] using C.base_densitySq_eq
  have hTwo :
      2 * C.conformalFactor.logDensity z₀ =
        2 * u.logDensity z₀ :=
    Real.exp_injective hExp
  linarith

/--
%%handwave
name: Recovery of the original density from a pullback candidate
statement:
  Let $F:\Omega\to\mathbb H$ be a normalized branch and let $v$ be a pullback Liouville candidate satisfying $e^{2v}=|F'|^2/(\operatorname{Im}F)^2$. If $e^{2u(z)}=e^{2v(z)}$ at $z\in\Omega$, then $e^{2u(z)}=|F'(z)|^2/(\operatorname{Im}F(z))^2$.
proof:
  Replace the original squared density by the candidate squared density and apply the candidate's Poincare pullback formula.
-/
theorem pullback_eq_densitySq_of_eq_original
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    {z : ℂ} (hz : z ∈ N.domain)
    (hEq : u.densitySq z = C.conformalFactor.densitySq z) :
    u.densitySq z =
      Complex.normSq (N.normalized.projective.affineMapDeriv z) /
        ((N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2) := by
  rw [hEq, C.densitySq_eq_pullback z hz]

end LocalHyperbolicPullbackLiouvilleCandidate

/--
A metric-recovering upper-half-plane normalization of a local projective
Schwarzian solution.

Solving the Schwarzian equation first gives a projective map only up to
postcomposition by a Mobius transformation.  In the hyperbolic case the missing
normalization theorem should choose such a postcomposition so that, on a
possibly smaller domain, the finite affine chart lands in `ℍ` and pulls the
Poincare squared density back to `exp (2u)`.
-/
structure LocalMetricRecoveringUpperHalfPlaneNormalization {u : LocalConformalFactor}
    {S : LocalSchwarzianData u} (D : LocalProjectiveDevelopingMap S) where
  /-- The normalized, metric-recovering upper-half-plane developing map. -/
  normalized : LocalUpperHalfPlaneDevelopingMap S
  /-- Mobius postcomposition used to normalize the original projective map. -/
  postcomposition : MobiusRepresentative
  /-- The normalized domain is a shrink of the original projective solution domain. -/
  domain_subset_original : normalized.domain ⊆ D.domain
  /--
  The normalized projective map is obtained from the original one by Mobius
  postcomposition on the shrunk domain.
  -/
  projective_eq_postcompose_original :
    ∀ z, z ∈ normalized.domain →
      normalized.projective.projectiveMap z = postcomposition • D.projectiveMap z

namespace LocalMetricRecoveringUpperHalfPlaneNormalization

/--
Build a metric-recovering normalization from a 2-jet normalized
upper-half-plane candidate once the metric-recovery formula has been proved.

%%handwave
name:
  Metric-recovering branch from a two-jet normalization
statement:
  If a two-jet-normalized branch $F$ satisfies $e^{2u}=|F'|^2/(\operatorname{Im}F)^2$ on its domain, package it as a metric-recovering upper-half-plane normalization of the original projective branch.
-/
def ofTwoJetNormalization
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (hDensity :
      ∀ z, z ∈ N.domain →
        u.densitySq z =
          Complex.normSq (N.normalized.projective.affineMapDeriv z) /
            ((N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2)) :
    LocalMetricRecoveringUpperHalfPlaneNormalization D where
  normalized := N.normalized.toLocalUpperHalfPlaneDevelopingMap hDensity
  postcomposition := N.normalized.postcomposition
  domain_subset_original := N.normalized.domain_subset_original
  projective_eq_postcompose_original := N.normalized.projective_eq_postcompose_original

end LocalMetricRecoveringUpperHalfPlaneNormalization

end

end JJMath
