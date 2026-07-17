# Hyperbolic Metrics and Projective Structures

Let $X$ be a Riemann surface. A hyperbolic metric is locally written

\[
  g=e^{2u}|dz|^2,
\]

with Gaussian curvature $-1$. A complex projective structure is an atlas with
values in $\mathbb{CP}^1$ and Möbius transition maps. The bridge between them
is a developing map

\[
  \operatorname{dev}:\widetilde X_{x_0}\longrightarrow\mathbb H
\]

which pulls the Poincaré metric back to the lift of $g$ and is equivariant for
a representation of $\pi_1(X,x_0)$ in $\mathrm{PSL}_2(\mathbb R)$.

@include{lean:JJMath.HyperbolicMetric}

@include{lean:JJMath.ComplexProjectiveStructure}

@include{lean:JJMath.HyperbolicDevelopingMap}

## From Real Projective Holonomy to a Hyperbolic Metric

The complement of $\mathbb{RP}^1$ in $\mathbb{CP}^1$ is the union of the upper
and lower half-planes. On its affine part the squared Poincaré density is

\[
  \lambda_{\mathbb H}(z)^2=\frac{1}{(\operatorname{Im}z)^2}.
\]

This is the Poincaré metric of constant Gaussian curvature $-1$.

@include{lean:JJMath.poincareDensitySqInChart_gaussianCurvature_eq_minus_one}

A real projective transformation preserves both the real projective line and
this density. Consequently a projective developing map with
$\mathrm{PGL}_2(\mathbb R)$ holonomy pulls the density back consistently away
from the inverse image of $\mathbb{RP}^1$.

@include{lean:JJMath.pgl2r_preserves_offRealLineDensity}

The resulting metric is smooth and has curvature $-1$ on this regular locus.
It is naturally a singular hyperbolic metric on $X$, with the real-projective
locus recorded as its singular set.

@include{lean:JJMath.ComplexProjectiveStructure.induceSingularHyperbolicMetric}

This is the general projective-to-metric direction. When the developing map
already takes values in one half-plane, the real-projective locus is absent
and the pullback is an ordinary hyperbolic metric.

## From Curvature to a Holomorphic Schwarzian

For $g=e^{2u}|dz|^2$, the curvature equation and the Liouville equation are
equivalent:

\[
  K_g=-e^{-2u}\Delta u,
  \qquad
  K_g=-1 \Longleftrightarrow \Delta u=e^{2u}.
\]

@include{lean:JJMath.LocalConformalFactor.hasGaussianCurvature_iff_solvesConstantCurvatureEquation}

The local projective connection associated with $u$ is

\[
  Q=2(u_{zz}-u_z^2).
\]

Differentiating $u_{z\bar z}=\tfrac14e^{2u}$ in the $z$-direction shows that
$\partial_{\bar z}u_{zz}$ and $\partial_{\bar z}(u_z^2)$ are equal. Hence
$\partial_{\bar z}Q=0$, so $Q$ is holomorphic.

@include{lean:JJMath.hyperbolicLiouvilleProducesMetricSchwarzianDataTheorem}

## Solving and Normalizing the Schwarzian Equation

Given a holomorphic $Q$, consider

\[
  y''+\frac12Qy=0.
\]

If $y_0,y_1$ are two solutions with nonzero denominator and Wronskian, their
ratio $f=y_1/y_0$ has Schwarzian derivative $\{f,z\}=Q$.

@include{lean:JJMath.SchwarzianLinearODESolutionPair.schwarzianExpression_eq_coefficient}

The required pair is constructed locally by Frobenius series with initial
conditions

\[
  y_0(z_0)=1,\quad y_0'(z_0)=0,
  \qquad
  y_1(z_0)=0,\quad y_1'(z_0)=1.
\]

After shrinking, $y_0$ and the Wronskian remain nonzero.

@include{lean:JJMath.holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic}

The quotient initially gives a projective coordinate. A Möbius
postcomposition is then chosen to impose the hyperbolic two-jet

\[
  F(z_0)=i,\qquad
  F'(z_0)=e^{u(z_0)},\qquad
  F''(z_0)=F'(z_0)\bigl(2u_z(z_0)-iF'(z_0)\bigr).
\]

Since the normalized value is $i$, continuity allows a further restriction on
which $F$ takes values in $\mathbb H$.

@include{lean:JJMath.localProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem}

For the normalized branch, set

\[
  v=\log|F'|-\log\operatorname{Im}F.
\]

The Poincaré pullback calculation makes $v$ a Liouville solution with the same
metric Schwarzian as $u$, while the prescribed two-jet gives
$v(z_0)=u(z_0)$ and $v_z(z_0)=u_z(z_0)$. Local
Liouville--Schwarzian uniqueness therefore yields $v=u$ and hence

\[
  e^{2u(z)}=\frac{|F'(z)|^2}{(\operatorname{Im}F(z))^2}.
\]

@include{lean:JJMath.hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_liouvilleUniqueness}

Putting the curvature calculation, Frobenius construction, normalization,
metric recovery, and overlap uniqueness together gives a local atlas of
upper-half-plane branches. On every connected nonempty overlap, two branches
differ by an element of $\mathrm{PSL}_2(\mathbb R)$.

@include{lean:JJMath.solveLocalSchwarzianProblem}

The overlap comparison first matches the values and oriented tangent vectors
of two metric-recovering branches by a real Möbius transformation. Equality of
their Schwarzian coefficients then makes this comparison locally unique, and
a connectedness argument extends it across the whole overlap.

@include{lean:JJMath.metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem}

@include{lean:JJMath.pointedRealMobiusTransition_oneJetExtendsOnPreconnectedOverlap_of_pairProjectiveDerivative_coefficientAgreement}

## Analytic Continuation and the Developing Map

Fix $x_0\in X$ and one local branch at $x_0$. Continue it along a path by
choosing finitely many branch domains covering the path and composing their
real Möbius transitions. Refinement does not alter the result because repeated
charts contribute the identity and the transition maps satisfy the cocycle
law.

@include{lean:JJMath.HyperbolicMetric.exists_pathLocalTransitionModelBasedWeakHandoffSkeleton}

@include{lean:JJMath.HyperbolicMetric.pathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple_unconditional}

For two endpoint-fixed homotopic paths, compactness of the homotopy square
provides a finite grid subordinate to the branch domains. Sliding the path
across one rectangle preserves the terminal branch, so a finite sequence of
slides proves homotopy invariance.

@include{lean:JJMath.HyperbolicMetric.PathLocalTransitionBasedWeakHandoffHomotopyGridWalkPrinciple}

@include{lean:JJMath.HyperbolicMetric.PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalValue_homotopic}

Thus continuation depends only on a point of the based universal cover and
defines an equivariant holomorphic local biholomorphism
$\operatorname{dev}:\widetilde X_{x_0}\to\mathbb H$. Projectivizing
$\mathbb H\subset\mathbb{CP}^1$ and composing with local sections of the
covering map gives projective charts on $X$.

@include{lean:JJMath.HyperbolicMetric.PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.dev_deckAction_eq_of_terminal_path_equivariant}

@include{lean:JJMath.HyperbolicMetric.canonicalLocalTransitionAgreement_dev_pullsBackMetric}

@include{lean:JJMath.ProjectivizedHyperbolicDevelopingMap}

@include{lean:JJMath.ProjectiveAtlasFromDevelopingMap}

@include{lean:JJMath.HyperbolicMetric.psl2rProjectiveStructureOfProjectivizedDevelopingMap}

@include{lean:JJMath.ProjectiveAtlasFromDevelopingMap.hasPSL2RHolonomy}

The resulting atlas is compatible with the original complex structure, is
induced by the given metric through the Poincaré pullback identity, and has
holonomy in $\mathrm{PSL}_2(\mathbb R)$.

@include{lean:JJMath.HyperbolicMetric.complete_partial_converse_theorem}
