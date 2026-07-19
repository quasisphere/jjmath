import JJMath.Hyperbolic.Schwarzian.Theorems.LocalMaps

/-!
# Split Schwarzian theorem wrappers and hyperbolic specialization
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems

end HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems

/--
Sharper bundled local boundary for producing real upper-half-plane branch
atlases from a hyperbolic Liouville factor.

Compared with `HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems`, this
replaces the broad branch-level real-transition input by the actual
atlas-level input still needed downstream: distinct metric-recovering branches
with nonempty overlap have real Mobius transitions.  The diagonal and empty
overlap cases are handled formally by the local atlas machinery.
-/
structure HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems where
  /-- Hyperbolic Liouville factors produce holomorphic local Schwarzian data. -/
  holomorphicSchwarzian : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
  /-- Local projective Schwarzian maps admit the prescribed hyperbolic 2-jet normalization. -/
  twoJetNormalization : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem
  /-- The Riccati analytic boundary gives metric recovery for the normalized 2-jet. -/
  riccatiBoundary : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems
  /-- Distinct overlapping metric-recovering atlas branches have real Mobius transitions. -/
  overlappingOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem

namespace HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems

end HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems

/--
Sharper bundled local boundary for producing real upper-half-plane branch
atlases from a hyperbolic Liouville factor.

This has the same downstream fields as
`HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems`, but asks for the
concrete Riccati calculus package.  The algebraic conversion to the older
Riccati analytic boundary is proved above.
-/
structure HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems where
  /-- Hyperbolic Liouville factors produce holomorphic local Schwarzian data. -/
  holomorphicSchwarzian : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
  /-- Local projective Schwarzian maps admit the prescribed hyperbolic 2-jet normalization. -/
  twoJetNormalization : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem
  /-- Concrete Riccati calculus plus the pullback calculation give metric recovery. -/
  riccatiCalculusBoundary : HyperbolicTwoJetRiccatiCalculusBoundaryTheorems
  /-- Metric-recovering upper-half-plane branches have real Mobius transitions. -/
  realTransitions : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem

namespace HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems

/-- Forget the concrete Riccati calculus provenance, retaining the older bundle. -/
def toAnalyticBoundary
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems) :
    HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems where
  holomorphicSchwarzian := B.holomorphicSchwarzian
  twoJetNormalization := B.twoJetNormalization
  riccatiBoundary := B.riccatiCalculusBoundary.toRiccatiAnalyticBoundary
  realTransitions := B.realTransitions

end HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems

/--
Sharpest local boundary currently recorded for the local converse.

This is the same theorem package as
`HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems`, but its Riccati field
uses the canonical Frechet-Wirtinger derivatives of the original and pullback
conformal factors.
-/
structure HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems where
  /-- Hyperbolic Liouville factors produce holomorphic local Schwarzian data. -/
  holomorphicSchwarzian : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
  /-- Local projective Schwarzian maps admit the prescribed hyperbolic 2-jet normalization. -/
  twoJetNormalization : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem
  /-- Pullback calculation plus canonical Riccati calculus give metric recovery. -/
  canonicalRiccatiBoundary : HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems
  /-- Metric-recovering upper-half-plane branches have real Mobius transitions. -/
  realTransitions : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem

namespace HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems

/-- Forget to the concrete-calculus local boundary. -/
def toCalculusBoundary
    (B : HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems) :
    HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems where
  holomorphicSchwarzian := B.holomorphicSchwarzian
  twoJetNormalization := B.twoJetNormalization
  riccatiCalculusBoundary := B.canonicalRiccatiBoundary.toRiccatiCalculusBoundary
  realTransitions := B.realTransitions

/-- Forget to the older analytic-boundary package. -/
def toAnalyticBoundary
    (B : HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems) :
    HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems :=
  B.toCalculusBoundary.toAnalyticBoundary

end HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems

/--
Full local boundary using the corrected Frechet-Wirtinger Riccati route.

This is the atlas-level counterpart of the corrected local-map boundary below:
it keeps the usual holomorphic-Schwarzian, two-jet normalization, and
real-transition inputs, but uses the metric-scaled Wirtinger-Riccati
metric-recovery package instead of the older canonical Riccati calculus bundle.
-/
structure HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems where
  /-- Hyperbolic Liouville factors produce holomorphic local Schwarzian data. -/
  holomorphicSchwarzian : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
  /-- Local projective Schwarzian maps admit the prescribed hyperbolic 2-jet normalization. -/
  twoJetNormalization : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem
  /-- Pullback derivative-identification plus corrected Wirtinger-Riccati metric recovery. -/
  derivIdentifiedCanonicalMetricWirtingerBoundary :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems
  /-- Metric-recovering upper-half-plane branches have real Mobius transitions. -/
  realTransitions : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem

namespace HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems

end HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems

/--
Smallest local-map boundary currently recorded for the local converse.

The holomorphic-Schwarzian, Frobenius existence, normal-form chain rule, and
upper-half-plane landing parts are all supplied internally.  The only remaining
local-map input is the derivative-identified canonical pullback/Riccati
metric-recovery package.
-/
structure HyperbolicLiouvilleSchwarzianLocalMapCanonicalBoundaryTheorems where
  /-- Pullback derivative-identification plus canonical Riccati metric recovery. -/
  derivIdentifiedCanonicalBoundary :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems

namespace HyperbolicLiouvilleSchwarzianLocalMapCanonicalBoundaryTheorems

end HyperbolicLiouvilleSchwarzianLocalMapCanonicalBoundaryTheorems

/--
Smallest local-map boundary using the corrected Frechet-Wirtinger Riccati
route.

Compared with `HyperbolicLiouvilleSchwarzianLocalMapCanonicalBoundaryTheorems`,
this replaces the older canonical Riccati calculus side by the honest
metric-scaled Wirtinger-Riccati theorem.
-/
structure HyperbolicLiouvilleSchwarzianLocalMapMetricWirtingerBoundaryTheorems where
  /-- Pullback derivative-identification plus corrected Wirtinger-Riccati metric recovery. -/
  derivIdentifiedCanonicalMetricWirtingerBoundary :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems

namespace HyperbolicLiouvilleSchwarzianLocalMapMetricWirtingerBoundaryTheorems

end HyperbolicLiouvilleSchwarzianLocalMapMetricWirtingerBoundaryTheorems

/--
Local-map boundary using derivative algebra and the corrected
Frechet-Wirtinger Riccati route.

The Poincare Laplacian calculation is not an input: derivative algebra is
converted to actual affine derivative algebra, and the mixed-expression
calculation supplies the Laplacian field.
-/
structure HyperbolicLiouvilleSchwarzianLocalMapDerivativeAlgebraMetricWirtingerBoundaryTheorems where
  /-- Derivative algebra plus corrected Wirtinger-Riccati metric recovery. -/
  derivativeAlgebraCanonicalMetricWirtingerBoundary :
    HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

namespace HyperbolicLiouvilleSchwarzianLocalMapDerivativeAlgebraMetricWirtingerBoundaryTheorems

end HyperbolicLiouvilleSchwarzianLocalMapDerivativeAlgebraMetricWirtingerBoundaryTheorems

/--
Smallest local-map boundary using actual affine branch derivative data and the
corrected Frechet-Wirtinger Riccati route.

This is the concrete local version of the current remaining analytic boundary:
the pullback side is stated with `HasDerivAt` inputs rather than already
identified `deriv` fields.
-/
structure HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeMetricWirtingerBoundaryTheorems where
  /-- Affine derivative pullback data plus corrected Wirtinger-Riccati metric recovery. -/
  affineDerivativeCanonicalMetricWirtingerBoundary :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems

namespace HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeMetricWirtingerBoundaryTheorems

end HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeMetricWirtingerBoundaryTheorems

/--
Smallest local-map boundary using actual affine branch derivative algebra and
the corrected Frechet-Wirtinger Riccati route.

Compared with
`HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeMetricWirtingerBoundaryTheorems`,
this does not ask for a Poincare Laplacian field.  The Laplacian identity is
derived from the explicit mixed-expression calculation.
-/
structure HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeAlgebraMetricWirtingerBoundaryTheorems where
  /--
  Affine derivative algebra plus corrected Wirtinger-Riccati metric recovery.
  -/
  affineDerivativeAlgebraCanonicalMetricWirtingerBoundary :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

namespace HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeAlgebraMetricWirtingerBoundaryTheorems

/-- Forget to the older affine-derivative local-map boundary. -/
def toAffineDerivativeMetricWirtingerBoundary
    (B :
      HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeAlgebraMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeMetricWirtingerBoundaryTheorems where
  affineDerivativeCanonicalMetricWirtingerBoundary :=
    (B.affineDerivativeAlgebraCanonicalMetricWirtingerBoundary).toAffineDerivativeCanonicalMetricWirtingerRiccatiBoundary

end HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeAlgebraMetricWirtingerBoundaryTheorems

end

end JJMath
