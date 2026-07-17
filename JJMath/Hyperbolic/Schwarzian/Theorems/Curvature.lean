import JJMath.Hyperbolic.Schwarzian.Developing

/-!
# Split Schwarzian theorem wrappers and hyperbolic specialization
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

/--
The local analytic theorem target: a constant-curvature conformal factor
produces a holomorphic Schwarzian coefficient.

The formal calculation of `∂_{\bar z} (u_zz - u_z ^ 2) = 0` is above, and the
Cauchy-Riemann bridge `∂_{\bar z} q = 0 ⇒ q` holomorphic is now formalized.
The remaining boundary is to derive the required Wirtinger identities from the
current smooth conformal factor and express the symbolic `∂_{\bar z}` equation
as `HasDBarZeroOn`.
-/
def ConstantCurvatureProducesHolomorphicSchwarzianTheorem : Prop :=
  ∀ (u : LocalConformalFactor) (K : ℝ),
    u.SolvesConstantCurvatureEquation K → Nonempty (LocalSchwarzianData u)

/--
Sharper target: constant curvature produces Schwarzian data together with the
proof that the stored coefficient is the metric Schwarzian of `u`.
-/
def ConstantCurvatureProducesMetricSchwarzianDataTheorem : Prop :=
  ∀ (u : LocalConformalFactor) (K : ℝ),
    u.SolvesConstantCurvatureEquation K → Nonempty (LocalMetricSchwarzianData u)

/--
Sharper analytic target: constant curvature first produces the unscaled
Liouville expression `q = u_zz - u_z ^ 2` with `∂_{\bar z} q = 0`.

The actual Schwarzian data then follows by multiplying this coefficient by `2`.
-/
def ConstantCurvatureProducesHalfSchwarzianDataTheorem : Prop :=
  ∀ (u : LocalConformalFactor) (K : ℝ),
    u.SolvesConstantCurvatureEquation K → Nonempty (LocalHalfSchwarzianData u)

/--
Concrete Frechet/Wirtinger derivative package target.

This is now the main low-level analytic boundary for producing the
half-Schwarzian coefficient from a constant-curvature conformal factor.  The
functions in the package are no longer arbitrary symbolic fields: they are the
canonical Frechet-level Wirtinger expressions built from `u.logDensity`.
-/
def ConstantCurvatureProducesWirtingerDerivativePackageTheorem : Prop :=
  ∀ (u : LocalConformalFactor) (K : ℝ),
    u.SolvesConstantCurvatureEquation K →
      Nonempty (u.WirtingerDerivativePackage K)

/--
The concrete Wirtinger package theorem follows from the named local analytic
axioms attached to `LocalConformalFactor`.
-/
theorem constantCurvatureProducesWirtingerDerivativePackageTheorem :
    ConstantCurvatureProducesWirtingerDerivativePackageTheorem := by
  intro u K hK
  exact ⟨u.wirtingerDerivativePackage K hK⟩

/--
The remaining bridge from symbolic Wirtinger product-rule data to the real
Cauchy-Riemann condition for the unscaled coefficient.

The product-rule calculation proves that the symbolic `dbarSchwarzian` field
vanishes.  This theorem target says that this vanishing is exactly the
`HasDBarZeroOn` condition used by mathlib's holomorphicity API.
-/
def ConstantCurvatureProductRuleDataGivesHalfSchwarzianTheorem : Prop :=
  ∀ (u : LocalConformalFactor) (K : ℝ) (P : SchwarzianProductRuleData u K),
    u.SolvesConstantCurvatureEquation K →
      (∀ z, z ∈ u.coordinateDomain → P.dbarSchwarzian z = 0) →
        HasDBarZeroOn P.schwarzianCoefficient u.coordinateDomain

/--
Sharper boundary for the symbolic product-rule package: the symbolic
`dbarSchwarzian` field is the Frechet/Wirtinger `∂_{\bar z}` value of the
unscaled Schwarzian coefficient.

Once this is available, the vanishing already proved by the product-rule
calculation automatically becomes the Cauchy-Riemann condition.
-/
def ConstantCurvatureProductRuleDataHasFrechetDBarTheorem : Prop :=
  ∀ (u : LocalConformalFactor) (K : ℝ) (P : SchwarzianProductRuleData u K),
    u.SolvesConstantCurvatureEquation K →
      HasFrechetDBarOn P.schwarzianCoefficient P.dbarSchwarzian u.coordinateDomain

/--
Identifying the symbolic product-rule `dbarSchwarzian` with the Frechet
Wirtinger operator closes the bridge to `HasDBarZeroOn`.
-/
theorem constantCurvatureProductRuleDataGivesHalfSchwarzianTheorem_of_frechetDBar
    (h : ConstantCurvatureProductRuleDataHasFrechetDBarTheorem) :
    ConstantCurvatureProductRuleDataGivesHalfSchwarzianTheorem := by
  intro u K P hK hzero
  exact (h u K P hK).hasDBarZeroOn_of_dbar_eq_zero hzero

/--
Product-rule data plus the symbolic-to-CR bridge gives the unscaled
half-Schwarzian target.
-/
theorem constantCurvatureProducesHalfSchwarzianDataTheorem_of_productRuleData
    (hData : ∀ (u : LocalConformalFactor) (K : ℝ),
      u.SolvesConstantCurvatureEquation K → Nonempty (SchwarzianProductRuleData u K))
    (hFormula : ∀ (u : LocalConformalFactor) (K : ℝ) (P : SchwarzianProductRuleData u K),
      u.SolvesConstantCurvatureEquation K →
        ∀ z, z ∈ u.coordinateDomain →
          P.schwarzianCoefficient z = u.halfSchwarzianCoefficient z)
    (hCR : ConstantCurvatureProductRuleDataGivesHalfSchwarzianTheorem) :
    ConstantCurvatureProducesHalfSchwarzianDataTheorem := by
  intro u K hK
  rcases hData u K hK with ⟨P⟩
  exact ⟨P.toLocalHalfSchwarzianData
    (hFormula u K P hK)
    (hCR u K P hK (P.dbarSchwarzian_eq_zero_of_solvesConstantCurvatureEquation hK))⟩

/--
Concrete Frechet/Wirtinger derivative packages give the unscaled
half-Schwarzian target directly.
-/
theorem constantCurvatureProducesHalfSchwarzianDataTheorem_of_wirtingerDerivativePackage
    (hW : ConstantCurvatureProducesWirtingerDerivativePackageTheorem) :
    ConstantCurvatureProducesHalfSchwarzianDataTheorem := by
  intro u K hK
  rcases hW u K hK with ⟨W⟩
  exact ⟨W.toLocalHalfSchwarzianData hK⟩

/--
The unscaled half-Schwarzian theorem now follows from the named analytic
axioms via the concrete Wirtinger package.
-/
theorem constantCurvatureProducesHalfSchwarzianDataTheorem :
    ConstantCurvatureProducesHalfSchwarzianDataTheorem :=
  constantCurvatureProducesHalfSchwarzianDataTheorem_of_wirtingerDerivativePackage
    constantCurvatureProducesWirtingerDerivativePackageTheorem

/-- The unscaled Liouville coefficient target implies the actual holomorphic Schwarzian target. -/
theorem constantCurvatureProducesHolomorphicSchwarzianTheorem_of_halfSchwarzian
    (h : ConstantCurvatureProducesHalfSchwarzianDataTheorem) :
    ConstantCurvatureProducesHolomorphicSchwarzianTheorem := by
  intro u K hK
  rcases h u K hK with ⟨H⟩
  exact ⟨H.toLocalSchwarzianData⟩

/--
Concrete Frechet/Wirtinger derivative packages give the actual holomorphic
Schwarzian target.
-/
theorem constantCurvatureProducesHolomorphicSchwarzianTheorem_of_wirtingerDerivativePackage
    (hW : ConstantCurvatureProducesWirtingerDerivativePackageTheorem) :
    ConstantCurvatureProducesHolomorphicSchwarzianTheorem :=
  constantCurvatureProducesHolomorphicSchwarzianTheorem_of_halfSchwarzian
    (constantCurvatureProducesHalfSchwarzianDataTheorem_of_wirtingerDerivativePackage hW)

/--
Concrete Frechet/Wirtinger derivative packages give metric Schwarzian data
with the original-side coefficient identification.
-/
theorem constantCurvatureProducesMetricSchwarzianDataTheorem_of_wirtingerDerivativePackage
    (hW : ConstantCurvatureProducesWirtingerDerivativePackageTheorem) :
    ConstantCurvatureProducesMetricSchwarzianDataTheorem := by
  intro u K hK
  rcases hW u K hK with ⟨W⟩
  exact ⟨W.toLocalMetricSchwarzianData hK⟩

/--
The metric Schwarzian data theorem follows from the named analytic axioms via
the concrete Wirtinger package.
-/
theorem constantCurvatureProducesMetricSchwarzianDataTheorem :
    ConstantCurvatureProducesMetricSchwarzianDataTheorem :=
  constantCurvatureProducesMetricSchwarzianDataTheorem_of_wirtingerDerivativePackage
    constantCurvatureProducesWirtingerDerivativePackageTheorem

/-- Forgetting the coefficient identification gives the older holomorphic Schwarzian target. -/
theorem constantCurvatureProducesHolomorphicSchwarzianTheorem_of_metricSchwarzianData
    (h : ConstantCurvatureProducesMetricSchwarzianDataTheorem) :
    ConstantCurvatureProducesHolomorphicSchwarzianTheorem := by
  intro u K hK
  rcases h u K hK with ⟨M⟩
  exact ⟨M.toLocalSchwarzianData⟩

/--
The actual holomorphic Schwarzian theorem now follows from the named analytic
axioms via the concrete Wirtinger package.
-/
theorem constantCurvatureProducesHolomorphicSchwarzianTheorem :
    ConstantCurvatureProducesHolomorphicSchwarzianTheorem :=
  constantCurvatureProducesHolomorphicSchwarzianTheorem_of_metricSchwarzianData
    constantCurvatureProducesMetricSchwarzianDataTheorem

/--
The next combined local theorem target: constant curvature produces local
solutions of the Schwarzian equation, hence local projective coordinates.
-/
def ConstantCurvatureProducesLocalSchwarzianODEChartsTheorem : Prop :=
  ∀ (u : LocalConformalFactor) (K : ℝ) ⦃z : ℂ⦄,
    u.SolvesConstantCurvatureEquation K → z ∈ u.coordinateDomain →
      ∃ (S : LocalSchwarzianData u) (C : LocalSchwarzianODEChart S), z ∈ C.domain

/--
Constant curvature produces local projective developing maps: in a small
coordinate ball the developing coordinate is the Riemann-sphere-valued
projectivization of a ratio of two normalized ODE solutions.
-/
def ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem : Prop :=
  ∀ (u : LocalConformalFactor) (K : ℝ) ⦃z : ℂ⦄,
    u.SolvesConstantCurvatureEquation K → z ∈ u.coordinateDomain →
      ∃ (S : LocalSchwarzianData u) (D : LocalProjectiveDevelopingMap S), z ∈ D.domain

/--
Metric-aware version of the local projective developing-map target.

This keeps the original metric-Schwarzian coefficient identification attached
to the chosen local coefficient, so later metric-recovery and transition
arguments do not have to rediscover that provenance.
-/
def ConstantCurvatureProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem : Prop :=
  ∀ (u : LocalConformalFactor) (K : ℝ) ⦃z : ℂ⦄,
    u.SolvesConstantCurvatureEquation K → z ∈ u.coordinateDomain →
      ∃ (M : LocalMetricSchwarzianData u)
        (D : LocalProjectiveDevelopingMap M.toLocalSchwarzianData), z ∈ D.domain

/-- Forgetting metric-Schwarzian provenance recovers the older local target. -/
def constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_metricSchwarzian
    (h : ConstantCurvatureProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem) :
    ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem := by
  intro u K z hK hz
  rcases h u K (z := z) hK hz with ⟨M, D, hDz⟩
  exact ⟨M.toLocalSchwarzianData, D, hDz⟩

/--
The holomorphic-Schwarzian theorem plus local ODE solvability gives local
Schwarzian ODE charts.
-/
def constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_schwarzian
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hODE : HolomorphicSchwarzianLocallySolvableTheorem) :
    ConstantCurvatureProducesLocalSchwarzianODEChartsTheorem := by
  intro u K z hK hz
  rcases hS u K hK with ⟨S⟩
  rcases hODE S hz with ⟨C, hCz⟩
  exact ⟨S, C, hCz⟩

/--
The holomorphic-Schwarzian theorem plus local projective-developing-map
solvability gives local projective developing maps.
-/
def constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_schwarzian
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hDev : HolomorphicSchwarzianLocalProjectiveDevelopingMapTheorem) :
    ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem := by
  intro u K z hK hz
  rcases hS u K hK with ⟨S⟩
  rcases hDev S hz with ⟨D, hDz⟩
  exact ⟨S, D, hDz⟩

/--
Metric-Schwarzian data plus local projective-developing-map solvability gives
metric-aware local projective developing maps.
-/
def constantCurvatureProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem_of_metricSchwarzian
    (hM : ConstantCurvatureProducesMetricSchwarzianDataTheorem)
    (hDev : HolomorphicSchwarzianLocalProjectiveDevelopingMapTheorem) :
    ConstantCurvatureProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem := by
  intro u K z hK hz
  rcases hM u K hK with ⟨M⟩
  rcases hDev M.toLocalSchwarzianData hz with ⟨D, hDz⟩
  exact ⟨M, D, hDz⟩

/-- Local Schwarzian ODE charts projectivize to local projective developing maps. -/
def constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_ODECharts
    (h : ConstantCurvatureProducesLocalSchwarzianODEChartsTheorem) :
    ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem := by
  intro u K z hK hz
  rcases h u K (z := z) hK hz with ⟨S, C, hCz⟩
  exact ⟨S, C.toLocalProjectiveDevelopingMap, hCz⟩

/--
The holomorphic-Schwarzian theorem plus Frobenius-pair existence gives local
Schwarzian ODE charts.
-/
def constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_frobenius
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    ConstantCurvatureProducesLocalSchwarzianODEChartsTheorem :=
  constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_schwarzian hS
    (holomorphicSchwarzianLocallySolvableTheorem_of_frobeniusPairExistence hFrob)

/--
The holomorphic-Schwarzian theorem plus Frobenius-pair existence gives local
projective developing maps.
-/
def constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem :=
  constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_schwarzian hS
    (holomorphicSchwarzianLocalProjectiveDevelopingMapTheorem_of_frobeniusPairExistence hFrob)

/--
Metric-Schwarzian data plus Frobenius-pair existence gives metric-aware local
projective developing maps.
-/
def constantCurvatureProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem_of_frobenius
    (hM : ConstantCurvatureProducesMetricSchwarzianDataTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    ConstantCurvatureProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem :=
  constantCurvatureProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem_of_metricSchwarzian
    hM
    (holomorphicSchwarzianLocalProjectiveDevelopingMapTheorem_of_frobeniusPairExistence hFrob)

/--
Concrete Frechet/Wirtinger derivative packages plus Frobenius-pair existence
give local Schwarzian ODE charts.
-/
def constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_wirtingerDerivativePackage
    (hW : ConstantCurvatureProducesWirtingerDerivativePackageTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    ConstantCurvatureProducesLocalSchwarzianODEChartsTheorem :=
  constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_frobenius
    (constantCurvatureProducesHolomorphicSchwarzianTheorem_of_wirtingerDerivativePackage hW)
    hFrob

/--
Concrete Frechet/Wirtinger derivative packages plus Frobenius-pair existence
give local projective developing maps.
-/
def constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_wirtingerDerivativePackage
    (hW : ConstantCurvatureProducesWirtingerDerivativePackageTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem :=
  constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius
    (constantCurvatureProducesHolomorphicSchwarzianTheorem_of_wirtingerDerivativePackage hW)
    hFrob

/--
The holomorphic-Schwarzian theorem plus pre-shrinking Frobenius existence and
nonvanishing shrink gives local Schwarzian ODE charts.
-/
def constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_frobeniusPrePair
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hPre : HolomorphicSchwarzianFrobeniusPrePairExistenceTheorem)
    (hShrink : CenteredFrobeniusNonvanishingShrinkTheorem) :
    ConstantCurvatureProducesLocalSchwarzianODEChartsTheorem :=
  constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_frobenius hS
    (holomorphicSchwarzianFrobeniusPairExistence_of_prePair_and_shrink hPre hShrink)

/--
The holomorphic-Schwarzian theorem plus pre-shrinking Frobenius existence and
nonvanishing shrink gives local projective developing maps.
-/
def constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_frobeniusPrePair
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hPre : HolomorphicSchwarzianFrobeniusPrePairExistenceTheorem)
    (hShrink : CenteredFrobeniusNonvanishingShrinkTheorem) :
    ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem :=
  constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius hS
    (holomorphicSchwarzianFrobeniusPairExistence_of_prePair_and_shrink hPre hShrink)

/--
The holomorphic-Schwarzian theorem plus pre-shrinking Frobenius existence gives
local Schwarzian ODE charts; the nonvanishing shrink is now proved internally.
-/
def constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_frobeniusPrePair'
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hPre : HolomorphicSchwarzianFrobeniusPrePairExistenceTheorem) :
    ConstantCurvatureProducesLocalSchwarzianODEChartsTheorem :=
  constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_frobenius hS
    (holomorphicSchwarzianFrobeniusPairExistence_of_prePair hPre)

/--
The holomorphic-Schwarzian theorem plus pre-shrinking Frobenius existence gives
local projective developing maps; the nonvanishing shrink is now proved
internally.
-/
def constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_frobeniusPrePair'
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hPre : HolomorphicSchwarzianFrobeniusPrePairExistenceTheorem) :
    ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem :=
  constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius hS
    (holomorphicSchwarzianFrobeniusPairExistence_of_prePair hPre)

/--
The holomorphic-Schwarzian theorem plus pre-shrinking Frobenius existence with
derivative-continuity data gives local Schwarzian ODE charts.
-/
def constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_frobeniusPrePairWithDerivativeContinuity
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hPre : HolomorphicSchwarzianFrobeniusPrePairWithDerivativeContinuityTheorem) :
    ConstantCurvatureProducesLocalSchwarzianODEChartsTheorem :=
  constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_frobenius hS
    (holomorphicSchwarzianFrobeniusPairExistence_of_prePairWithDerivativeContinuity hPre)

/--
The holomorphic-Schwarzian theorem plus pre-shrinking Frobenius existence with
derivative-continuity data gives local projective developing maps.
-/
def constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_frobeniusPrePairWithDerivativeContinuity
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hPre : HolomorphicSchwarzianFrobeniusPrePairWithDerivativeContinuityTheorem) :
    ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem :=
  constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius hS
    (holomorphicSchwarzianFrobeniusPairExistence_of_prePairWithDerivativeContinuity hPre)

/--
The holomorphic-Schwarzian theorem plus termwise Frobenius pre-pair existence
gives local Schwarzian ODE charts.
-/
def constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_termwiseFrobenius
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hTermwise : HolomorphicSchwarzianFrobeniusTermwisePrePairExistenceTheorem) :
    ConstantCurvatureProducesLocalSchwarzianODEChartsTheorem :=
  constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_frobenius hS
    (holomorphicSchwarzianFrobeniusPairExistence_of_termwise hTermwise)

/--
The holomorphic-Schwarzian theorem plus termwise Frobenius pre-pair existence
gives local projective developing maps.
-/
def constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_termwiseFrobenius
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hTermwise : HolomorphicSchwarzianFrobeniusTermwisePrePairExistenceTheorem) :
    ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem :=
  constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius hS
    (holomorphicSchwarzianFrobeniusPairExistence_of_termwise hTermwise)

/--
The holomorphic-Schwarzian theorem plus coefficient geometric majorants gives
local Schwarzian ODE charts.
-/
def constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_coefficientGeometricMajorant
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hCoeff : HolomorphicSchwarzianCoefficientGeometricMajorantTheorem) :
    ConstantCurvatureProducesLocalSchwarzianODEChartsTheorem :=
  constantCurvatureProducesLocalSchwarzianODEChartsTheorem_of_frobenius hS
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant hCoeff)

/--
The holomorphic-Schwarzian theorem plus coefficient geometric majorants gives
local projective developing maps.
-/
def constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_coefficientGeometricMajorant
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hCoeff : HolomorphicSchwarzianCoefficientGeometricMajorantTheorem) :
    ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem :=
  constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius hS
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant hCoeff)

/-- The hyperbolic specialization of the holomorphic-Schwarzian target. -/
def HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem : Prop :=
  ∀ (u : LocalConformalFactor),
    u.SolvesLiouvilleEquation → Nonempty (LocalSchwarzianData u)

/--
Hyperbolic specialization of the metric-Schwarzian target: the local
Schwarzian coefficient is not merely holomorphic, but is identified with the
canonical metric Schwarzian of the Liouville factor.
-/
def HyperbolicLiouvilleProducesMetricSchwarzianDataTheorem : Prop :=
  ∀ (u : LocalConformalFactor),
    u.SolvesLiouvilleEquation → Nonempty (LocalMetricSchwarzianData u)

/-- Hyperbolic specialization of the unscaled Liouville Schwarzian target. -/
def HyperbolicLiouvilleProducesHalfSchwarzianDataTheorem : Prop :=
  ∀ (u : LocalConformalFactor),
    u.SolvesLiouvilleEquation → Nonempty (LocalHalfSchwarzianData u)

/--
Hyperbolic specialization of the concrete Frechet/Wirtinger derivative package
target.
-/
def HyperbolicLiouvilleProducesWirtingerDerivativePackageTheorem : Prop :=
  ∀ (u : LocalConformalFactor),
    u.SolvesLiouvilleEquation → Nonempty (u.WirtingerDerivativePackage (-1))

/-- The unscaled hyperbolic target implies the actual holomorphic Schwarzian target. -/
theorem hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem_of_halfSchwarzian
    (h : HyperbolicLiouvilleProducesHalfSchwarzianDataTheorem) :
    HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem := by
  intro u hu
  rcases h u hu with ⟨H⟩
  exact ⟨H.toLocalSchwarzianData⟩

/-- Metric-Schwarzian data forgets to ordinary holomorphic Schwarzian data. -/
theorem hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem_of_metricSchwarzianData
    (h : HyperbolicLiouvilleProducesMetricSchwarzianDataTheorem) :
    HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem := by
  intro u hu
  rcases h u hu with ⟨M⟩
  exact ⟨M.toLocalSchwarzianData⟩

/--
Concrete Frechet/Wirtinger derivative packages give the unscaled hyperbolic
Liouville Schwarzian target.
-/
theorem hyperbolicLiouvilleProducesHalfSchwarzianDataTheorem_of_wirtingerDerivativePackage
    (hW : HyperbolicLiouvilleProducesWirtingerDerivativePackageTheorem) :
    HyperbolicLiouvilleProducesHalfSchwarzianDataTheorem := by
  intro u hu
  rcases hW u hu with ⟨W⟩
  exact ⟨W.toLocalHalfSchwarzianData
    ((u.solvesLiouvilleEquation_iff_solvesConstantCurvatureEquation_neg_one).mp hu)⟩

/--
Concrete Frechet/Wirtinger derivative packages give the actual hyperbolic
holomorphic Schwarzian target.
-/
theorem hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem_of_wirtingerDerivativePackage
    (hW : HyperbolicLiouvilleProducesWirtingerDerivativePackageTheorem) :
    HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem :=
  hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem_of_halfSchwarzian
    (hyperbolicLiouvilleProducesHalfSchwarzianDataTheorem_of_wirtingerDerivativePackage hW)

/--
The hyperbolic holomorphic Schwarzian theorem follows from the named analytic
axioms via the concrete Wirtinger package.
-/
theorem hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem :
    HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem :=
  fun u hu ↦
    constantCurvatureProducesHolomorphicSchwarzianTheorem u (-1)
      ((u.solvesLiouvilleEquation_iff_solvesConstantCurvatureEquation_neg_one).mp hu)

/--
%%handwave
name:
  Holomorphic metric Schwarzian
statement:
  If $u : U \to \mathbb R$ satisfies the hyperbolic Liouville equation
  $\Delta u=e^{2u}$, then
  $Q=2(u_{zz}-u_z^2)$ is holomorphic on $U$. Thus every hyperbolic conformal
  factor determines local holomorphic Schwarzian data with this coefficient.
proof:
  The identity $u_{z\bar z}=\tfrac14 e^{2u}$ and equality of mixed derivatives
  give
  $\partial_{\bar z}u_{zz}=\tfrac12u_z e^{2u}$, while the product rule gives
  $\partial_{\bar z}(u_z^2)=\tfrac12u_z e^{2u}$. Their difference is zero, and
  the Cauchy--Riemann criterion makes $u_{zz}-u_z^2$, hence $Q$, holomorphic.
tags:
  milestone
-/
theorem hyperbolicLiouvilleProducesMetricSchwarzianDataTheorem :
    HyperbolicLiouvilleProducesMetricSchwarzianDataTheorem :=
  fun u hu ↦
    constantCurvatureProducesMetricSchwarzianDataTheorem u (-1)
      ((u.solvesLiouvilleEquation_iff_solvesConstantCurvatureEquation_neg_one).mp hu)

/-- Hyperbolic specialization of the local Schwarzian ODE chart target. -/
def HyperbolicLiouvilleProducesLocalSchwarzianODEChartsTheorem : Prop :=
  ∀ (u : LocalConformalFactor) ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ u.coordinateDomain →
      ∃ (S : LocalSchwarzianData u) (C : LocalSchwarzianODEChart S), z ∈ C.domain

/-- Hyperbolic specialization of the local projective developing-map target. -/
def HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem : Prop :=
  ∀ (u : LocalConformalFactor) ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ u.coordinateDomain →
      ∃ (S : LocalSchwarzianData u) (D : LocalProjectiveDevelopingMap S), z ∈ D.domain

/--
Metric-aware hyperbolic specialization of the local projective developing-map
target.
-/
def HyperbolicLiouvilleProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem : Prop :=
  ∀ (u : LocalConformalFactor) ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ u.coordinateDomain →
      ∃ (M : LocalMetricSchwarzianData u)
        (D : LocalProjectiveDevelopingMap M.toLocalSchwarzianData), z ∈ D.domain

/-- Forgetting metric-Schwarzian provenance recovers the older hyperbolic local target. -/
theorem hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_metricSchwarzian
    (h : HyperbolicLiouvilleProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem := by
  intro u z hu hz
  rcases h u (z := z) hu hz with ⟨M, D, hDz⟩
  exact ⟨M.toLocalSchwarzianData, D, hDz⟩

/--
Metric-Schwarzian Liouville data plus local projective-developing-map
solvability gives the metric-aware local target.
-/
theorem hyperbolicLiouvilleProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem_of_metricSchwarzian
    (hM : HyperbolicLiouvilleProducesMetricSchwarzianDataTheorem)
    (hDev : HolomorphicSchwarzianLocalProjectiveDevelopingMapTheorem) :
    HyperbolicLiouvilleProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem := by
  intro u z hu hz
  rcases hM u hu with ⟨M⟩
  rcases hDev M.toLocalSchwarzianData hz with ⟨D, hDz⟩
  exact ⟨M, D, hDz⟩

/--
Metric-Schwarzian Liouville data plus Frobenius-pair existence gives the
metric-aware local projective developing-map target.
-/
theorem hyperbolicLiouvilleProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem_of_frobenius
    (hM : HyperbolicLiouvilleProducesMetricSchwarzianDataTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    HyperbolicLiouvilleProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem_of_metricSchwarzian
    hM
    (holomorphicSchwarzianLocalProjectiveDevelopingMapTheorem_of_frobeniusPairExistence hFrob)

/--
Pointwise local projective Schwarzian solutions plus metric-recovering
normalization give a metric-recovering Schwarzian pre-atlas.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_projectiveNormalization
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hNorm : HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem := by
  classical
  intro u hu
  let localProjective :
      ∀ z : u.coordinateDomain,
        Σ' S : LocalSchwarzianData u, Σ' D : LocalProjectiveDevelopingMap S,
          (z : ℂ) ∈ D.domain :=
    fun z ↦
      let h :
          ∃ (S : LocalSchwarzianData u) (D : LocalProjectiveDevelopingMap S),
            (z : ℂ) ∈ D.domain :=
        hProj u (z := (z : ℂ)) hu z.property
      ⟨Classical.choose h,
        Classical.choose (Classical.choose_spec h),
        Classical.choose_spec (Classical.choose_spec h)⟩
  let SAt : u.coordinateDomain → LocalSchwarzianData u :=
    fun z ↦ (localProjective z).1
  let DAt : ∀ z : u.coordinateDomain, LocalProjectiveDevelopingMap (SAt z) :=
    fun z ↦ (localProjective z).2.1
  have hDAt : ∀ z : u.coordinateDomain, (z : ℂ) ∈ (DAt z).domain := by
    intro z
    exact (localProjective z).2.2
  let localNormalization :
      ∀ z : u.coordinateDomain,
        Σ' N : LocalMetricRecoveringUpperHalfPlaneNormalization (DAt z),
          (z : ℂ) ∈ N.normalized.domain :=
    fun z ↦
      let h :
          ∃ N : LocalMetricRecoveringUpperHalfPlaneNormalization (DAt z),
            (z : ℂ) ∈ N.normalized.domain :=
        hNorm (SAt z) (DAt z) (z := (z : ℂ)) hu (hDAt z)
      ⟨Classical.choose h, Classical.choose_spec h⟩
  refine ⟨{
    schwarzianAt := SAt
    projectiveAt := DAt
    normalizationAt := fun z ↦ (localNormalization z).1
    mem_normalized_domain := ?_
  }⟩
  intro z
  exact (localNormalization z).2

/--
Pointwise local projective Schwarzian solutions plus the precise 2-jet
normalization and metric-recovery uniqueness theorem give a metric-recovering
Schwarzian pre-atlas.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_twoJetNormalization
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_projectiveNormalization
    hProj
    (hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
      hJet hRecovery)

/--
Pointwise local projective Schwarzian solutions plus precise 2-jet
normalization and the bundled Riccati analytic boundary give a
metric-recovering Schwarzian pre-atlas.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_twoJetRiccatiAnalyticBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_twoJetNormalization
    hProj hJet B.recoversMetric

/--
Pointwise local projective Schwarzian solutions plus precise 2-jet
normalization and the derivative-identified canonical pullback/Riccati boundary
give a metric-recovering Schwarzian pre-atlas.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_twoJetDerivIdentifiedBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_twoJetRiccatiAnalyticBoundary
    hProj hJet B.toRiccatiAnalyticBoundary

/--
Pointwise local projective Schwarzian solutions plus precise 2-jet
normalization and the derivative-identified pullback/corrected-Wirtinger
boundary give a metric-recovering Schwarzian pre-atlas.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_twoJetDerivIdentifiedMetricWirtingerBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_twoJetNormalization
    hProj hJet B.recoversMetric

/--
Pointwise local projective Schwarzian solutions plus precise 2-jet
normalization, actual affine pullback derivatives, and corrected
Wirtinger-Riccati uniqueness give a metric-recovering Schwarzian pre-atlas.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_twoJetAffineDerivativeMetricWirtingerBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_twoJetNormalization
    hProj hJet B.recoversMetric

/--
Pointwise local projective Schwarzian solutions plus precise two-jet
normalization and metric recovery produce a ball pre-atlas by retaining the
actual two-jet shrinkings.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetNormalization
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem := by
  classical
  intro u hu
  let localProjective :
      ∀ z : u.coordinateDomain,
        Σ' S : LocalSchwarzianData u, Σ' D : LocalProjectiveDevelopingMap S,
          (z : ℂ) ∈ D.domain :=
    fun z ↦
      let h :
          ∃ (S : LocalSchwarzianData u) (D : LocalProjectiveDevelopingMap S),
            (z : ℂ) ∈ D.domain :=
        hProj u (z := (z : ℂ)) hu z.property
      ⟨Classical.choose h,
        Classical.choose (Classical.choose_spec h),
        Classical.choose_spec (Classical.choose_spec h)⟩
  let SAt : u.coordinateDomain → LocalSchwarzianData u :=
    fun z ↦ (localProjective z).1
  let DAt : ∀ z : u.coordinateDomain, LocalProjectiveDevelopingMap (SAt z) :=
    fun z ↦ (localProjective z).2.1
  have hDAt : ∀ z : u.coordinateDomain, (z : ℂ) ∈ (DAt z).domain := by
    intro z
    exact (localProjective z).2.2
  let localTwoJet :
      ∀ z : u.coordinateDomain,
        Σ' N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization (DAt z) (z : ℂ),
          (z : ℂ) ∈ N.domain :=
    fun z ↦
      let h :
          ∃ N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization (DAt z) (z : ℂ),
            (z : ℂ) ∈ N.domain :=
        hJet (SAt z) (DAt z) hu (hDAt z)
      ⟨Classical.choose h, Classical.choose_spec h⟩
  let normalizationAt :
      ∀ z : u.coordinateDomain,
        LocalMetricRecoveringUpperHalfPlaneNormalization (DAt z) :=
    fun z ↦
      LocalMetricRecoveringUpperHalfPlaneNormalization.ofTwoJetNormalization
        (localTwoJet z).1 (hRecovery (SAt z) (localTwoJet z).1 hu)
  refine ⟨{
    schwarzianAt := SAt
    projectiveAt := DAt
    normalizationAt := normalizationAt
    mem_normalized_domain := ?_
    ball_domain := ?_
  }⟩
  · intro z
    exact (localTwoJet z).2
  · intro z
    rcases hyperbolicTwoJetNormalizationHasBallDomainTheorem
        (SAt z) (localTwoJet z).1 with ⟨c, r, hdomain⟩
    exact ⟨c, r, by
      simpa [normalizationAt, LocalMetricRecoveringUpperHalfPlaneNormalization.ofTwoJetNormalization,
        LocalUpperHalfPlaneDevelopingMap.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain] using hdomain⟩

/--
Pointwise local projective Schwarzian solutions plus the two-jet Riccati
boundary produce a ball pre-atlas by retaining the actual two-jet shrinkings.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetRiccatiAnalyticBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetNormalization
    hProj hJet B.recoversMetric

/--
Pointwise local projective Schwarzian solutions plus the
derivative-identified canonical pullback/Riccati boundary produce a ball
pre-atlas, using the ball domains already built into the two-jet
normalization package.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetDerivIdentifiedBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetRiccatiAnalyticBoundary
    hProj hJet B.toRiccatiAnalyticBoundary

/--
Pointwise local projective Schwarzian solutions plus the
derivative-identified pullback/corrected-Wirtinger boundary produce a ball
pre-atlas.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetDerivIdentifiedMetricWirtingerBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetNormalization
    hProj hJet B.recoversMetric

/--
Pointwise local projective Schwarzian solutions plus actual affine pullback
derivatives and corrected Wirtinger-Riccati uniqueness produce a ball
pre-atlas.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetAffineDerivativeMetricWirtingerBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetNormalization
    hProj hJet B.recoversMetric

/--
Projective Schwarzian local solvability, metric-recovering normalization, and
the overlap-shrinking target give the normalized-Schwarzian atlas target.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_projectiveNormalization
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hNorm : HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem)
    (hOverlap : MetricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_preAtlas
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_projectiveNormalization
      hProj hNorm)
    hOverlap

/--
Projective Schwarzian local solvability, precise 2-jet normalization,
metric-recovery uniqueness, and the overlap-shrinking target give the
normalized-Schwarzian atlas target.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetNormalization
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem)
    (hOverlap : MetricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_preAtlas
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_twoJetNormalization
      hProj hJet hRecovery)
    hOverlap

/--
Projective Schwarzian local solvability, precise 2-jet normalization, the
bundled Riccati analytic boundary, and overlap shrinking give the
metric-recovering normalization atlas target.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetRiccatiAnalyticBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems)
    (hOverlap : MetricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_preAtlas
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_twoJetRiccatiAnalyticBoundary
      hProj hJet B)
    hOverlap

/--
Projective Schwarzian local solvability, precise 2-jet normalization, the
derivative-identified canonical pullback/Riccati boundary, and overlap
shrinking give the metric-recovering normalization atlas target.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetDerivIdentifiedBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems)
    (hOverlap : MetricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetRiccatiAnalyticBoundary
    hProj hJet B.toRiccatiAnalyticBoundary hOverlap

/--
Projective Schwarzian local solvability, precise 2-jet normalization, the
derivative-identified pullback/corrected-Wirtinger boundary, and overlap
shrinking give the metric-recovering normalization atlas target.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetDerivIdentifiedMetricWirtingerBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems)
    (hOverlap : MetricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetNormalization
    hProj hJet B.recoversMetric hOverlap

/--
Projective Schwarzian local solvability, precise 2-jet normalization, actual
affine pullback derivatives, corrected Wirtinger-Riccati uniqueness, and
overlap shrinking give the metric-recovering normalization atlas target.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetAffineDerivativeMetricWirtingerBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems)
    (hOverlap : MetricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetNormalization
    hProj hJet B.recoversMetric hOverlap

/--
Projective Schwarzian local solvability, precise 2-jet normalization, and
metric recovery give the metric-recovering normalization atlas target by
retaining ball-shaped two-jet branch domains.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetNormalizationBallPreAtlas
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_ballPreAtlas
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetNormalization
      hProj hJet hRecovery)

/--
Projective Schwarzian local solvability, precise 2-jet normalization, and the
bundled Riccati analytic boundary give the metric-recovering normalization
atlas target by retaining ball-shaped two-jet branch domains.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetRiccatiAnalyticBoundaryBallPreAtlas
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetNormalizationBallPreAtlas
    hProj hJet B.recoversMetric

/--
Projective Schwarzian local solvability, precise 2-jet normalization, and the
derivative-identified canonical pullback/Riccati boundary give the
metric-recovering normalization atlas target by retaining ball-shaped two-jet
branch domains.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetDerivIdentifiedBoundaryBallPreAtlas
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_ballPreAtlas
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetDerivIdentifiedBoundary
      hProj hJet B)

/--
Projective Schwarzian local solvability, precise 2-jet normalization, and the
derivative-identified pullback/corrected-Wirtinger boundary give the
metric-recovering normalization atlas target by retaining ball-shaped two-jet
branch domains.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetDerivIdentifiedMetricWirtingerBoundaryBallPreAtlas
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_ballPreAtlas
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetDerivIdentifiedMetricWirtingerBoundary
      hProj hJet B)

/--
Projective Schwarzian local solvability, precise 2-jet normalization, actual
affine pullback derivatives, and corrected Wirtinger-Riccati uniqueness give
the metric-recovering normalization atlas target by retaining ball-shaped
two-jet branch domains.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetAffineDerivativeMetricWirtingerBoundaryBallPreAtlas
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_ballPreAtlas
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetAffineDerivativeMetricWirtingerBoundary
      hProj hJet B)

/--
Projective Schwarzian local solvability, precise 2-jet normalization, the
bundled Riccati analytic boundary, and ball-shaped branch domains give the
metric-recovering normalization atlas target.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetRiccatiAnalyticBoundaryBallDomains
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems)
    (hBall : MetricRecoveringSchwarzianPreAtlasHasBallDomainsTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_preAtlasBallDomains
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_twoJetRiccatiAnalyticBoundary
      hProj hJet B)
    hBall

/--
Local projective Schwarzian maps, precise 2-jet normalization, metric-recovery
uniqueness, overlap shrinking, and real-transition uniqueness give real
upper-half-plane branch atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_twoJetNormalization
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem)
    (hOverlap : MetricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetNormalization
      hProj hJet hRecovery hOverlap)
    hTransition

/--
Projective Schwarzian local solvability, precise 2-jet normalization, the
bundled Riccati analytic boundary, overlap shrinking, and real-transition
uniqueness give real upper-half-plane branch atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_twoJetRiccatiAnalyticBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems)
    (hOverlap : MetricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetRiccatiAnalyticBoundary
      hProj hJet B hOverlap)
    hTransition

/--
Projective Schwarzian local solvability, precise 2-jet normalization, the
derivative-identified canonical pullback/Riccati boundary, overlap shrinking,
and real-transition uniqueness give real upper-half-plane branch atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_twoJetDerivIdentifiedBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems)
    (hOverlap : MetricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_twoJetRiccatiAnalyticBoundary
    hProj hJet B.toRiccatiAnalyticBoundary hOverlap hTransition

/--
Projective Schwarzian local solvability, precise 2-jet normalization, the
derivative-identified pullback/corrected-Wirtinger boundary, overlap shrinking,
and real-transition uniqueness give real upper-half-plane branch atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_twoJetDerivIdentifiedMetricWirtingerBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems)
    (hOverlap : MetricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_twoJetNormalization
    hProj hJet B.recoversMetric hOverlap hTransition

/--
Projective Schwarzian local solvability, precise 2-jet normalization, actual
affine pullback derivatives, corrected Wirtinger-Riccati uniqueness, overlap
shrinking, and real-transition uniqueness give real upper-half-plane branch
atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_twoJetAffineDerivativeMetricWirtingerBoundary
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems)
    (hOverlap : MetricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_twoJetNormalization
    hProj hJet B.recoversMetric hOverlap hTransition

/--
Local projective Schwarzian maps, precise 2-jet normalization, the bundled
Riccati analytic boundary, and real-transition uniqueness give real
upper-half-plane branch atlases; the overlap connectedness is obtained from
the retained ball-shaped two-jet domains.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_twoJetRiccatiAnalyticBoundaryBallPreAtlas
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetRiccatiAnalyticBoundaryBallPreAtlas
      hProj hJet B)
    hTransition

/--
Local projective Schwarzian maps, precise 2-jet normalization, the
derivative-identified canonical pullback/Riccati boundary, and real-transition
uniqueness give real upper-half-plane branch atlases; the overlap connectedness
is obtained from the retained ball-shaped two-jet domains.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_twoJetDerivIdentifiedBoundaryBallPreAtlas
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetDerivIdentifiedBoundaryBallPreAtlas
      hProj hJet B)
    hTransition

/--
Local projective Schwarzian maps, precise 2-jet normalization, the
derivative-identified pullback/corrected-Wirtinger boundary, and
real-transition uniqueness give real upper-half-plane branch atlases; the
overlap connectedness is obtained from the retained ball-shaped two-jet
domains.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_twoJetDerivIdentifiedMetricWirtingerBoundaryBallPreAtlas
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetDerivIdentifiedMetricWirtingerBoundaryBallPreAtlas
      hProj hJet B)
    hTransition

/--
Local projective Schwarzian maps, precise 2-jet normalization, actual affine
pullback derivatives, corrected Wirtinger-Riccati uniqueness, and
real-transition uniqueness give real upper-half-plane branch atlases; the
overlap connectedness is obtained from the retained ball-shaped two-jet
domains.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_twoJetAffineDerivativeMetricWirtingerBoundaryBallPreAtlas
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetAffineDerivativeMetricWirtingerBoundaryBallPreAtlas
      hProj hJet B)
    hTransition

/--
Local projective Schwarzian maps, precise 2-jet normalization, actual affine
pullback derivatives, corrected Wirtinger-Riccati uniqueness, and
off-diagonal real-transition uniqueness give real upper-half-plane branch
atlases.  The diagonal branch transition is the identity real Mobius map, and
the overlap connectedness is obtained from retained ball-shaped two-jet
domains.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_twoJetAffineDerivativeMetricWirtingerBoundaryBallPreAtlasOffDiagonal
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems)
    (hOff :
      MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering_offDiagonal
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetAffineDerivativeMetricWirtingerBoundaryBallPreAtlas
      hProj hJet B)
    hOff

/--
Projective Schwarzian local solvability, precise 2-jet normalization, the
bundled Riccati analytic boundary, ball-shaped branch domains, and
real-transition uniqueness give real upper-half-plane branch atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_twoJetRiccatiAnalyticBoundaryBallDomains
    (hProj : HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem)
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems)
    (hBall : MetricRecoveringSchwarzianPreAtlasHasBallDomainsTheorem)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_twoJetRiccatiAnalyticBoundaryBallDomains
      hProj hJet B hBall)
    hTransition

/--
Hyperbolic Liouville data produces genuine local `ℍ`-valued developing maps
with the Poincare pullback squared-density formula.
-/
def HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem : Prop :=
  ∀ (u : LocalConformalFactor) ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ u.coordinateDomain →
      ∃ (S : LocalSchwarzianData u) (H : LocalUpperHalfPlaneDevelopingMap S),
        z ∈ H.domain

/--
Holomorphic Schwarzian data, Frobenius ODE existence, Frobenius Mobius
two-jet transitivity, and upper-half-plane landing give Frobenius two-jet
normalizations.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_mobius
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hMobius : LocalProjectiveFrobeniusMobiusTwoJetTransitivityTheorem)
    (hUpper : HyperbolicProjectiveTwoJetNormalizationLandsInUpperHalfPlaneTheorem) :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem := by
  intro u z hu hz
  rcases hS u hu with ⟨S⟩
  rcases hFrob S hz with ⟨a, ⟨P⟩⟩
  have hzP : z ∈ P.toLocalProjectiveDevelopingMap.domain := by
    simpa [CenteredNormalizedSchwarzianFrobeniusPair.toLocalProjectiveDevelopingMap,
      CenteredNormalizedSchwarzianFrobeniusPair.toLocalSchwarzianODEChart,
      LocalSchwarzianODEChart.toLocalProjectiveDevelopingMap] using
      mem_centeredBallDomain_center P.radius_pos
  rcases hyperbolicSchwarzianBaseJetExistenceTheorem hu
      (P.toLocalProjectiveDevelopingMap.domain_subset hzP) with ⟨J⟩
  rcases hMobius P hzP J.toNondegenerateFiniteTwoJet with ⟨M, _hMz⟩
  rcases hUpper S J M hu with ⟨N, _hNM, hNz⟩
  exact ⟨S, a, P, N, hNz⟩

/--
For Frobenius-produced projective maps, explicit Schwarzian invariance plus the
older upper-half-plane landing boundary gives the prescribed hyperbolic two-jet
normalizations.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_schwarzian
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hSchwarzian :
      LocalProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem)
    (hUpper : HyperbolicProjectiveTwoJetNormalizationLandsInUpperHalfPlaneTheorem) :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem :=
  hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_mobius
    hS hFrob
    (localProjectiveFrobeniusMobiusTwoJetTransitivityTheorem_of_schwarzian
      hSchwarzian)
    hUpper

/--
The holomorphic-Schwarzian theorem, Frobenius existence, and upper-half-plane
landing give Frobenius two-jet normalizations; explicit Schwarzian invariance
is now proved internally.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hUpper : HyperbolicProjectiveTwoJetNormalizationLandsInUpperHalfPlaneTheorem) :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem :=
  hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_schwarzian
    hS hFrob localProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem hUpper

/--
Holomorphic Schwarzian data, Frobenius existence, and the sharp explicit
normal-form `ℍ`-lift boundary give Frobenius two-jet normalizations, avoiding
the older broad arbitrary-map upper-half-plane landing theorem.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_normalFormLift
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hLift : LocalProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem) :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem := by
  intro u z hu hz
  rcases hS u hu with ⟨S⟩
  rcases hFrob S hz with ⟨a, ⟨P⟩⟩
  have hzP : z ∈ P.toLocalProjectiveDevelopingMap.domain := by
    simpa [CenteredNormalizedSchwarzianFrobeniusPair.toLocalProjectiveDevelopingMap,
      CenteredNormalizedSchwarzianFrobeniusPair.toLocalSchwarzianODEChart,
      LocalSchwarzianODEChart.toLocalProjectiveDevelopingMap] using
      mem_centeredBallDomain_center P.radius_pos
  rcases hyperbolicSchwarzianBaseJetExistenceTheorem hu
      (P.toLocalProjectiveDevelopingMap.domain_subset hzP) with ⟨J⟩
  rcases
      (localProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem_of_lift
        hLift) P hzP J with
    ⟨N, _hNJ, hNz⟩
  exact ⟨S, a, P, N, hNz⟩

/--
Holomorphic Schwarzian data, Frobenius existence, and a Frobenius-specific
upper-half-plane normalization theorem give Frobenius two-jet normalizations.
This is the common bridge used by the lift, derivative-identification, and
canonical third-derivative routes.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_normalFormNormalization
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hNorm : LocalProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem) :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem := by
  intro u z hu hz
  rcases hS u hu with ⟨S⟩
  rcases hFrob S hz with ⟨a, ⟨P⟩⟩
  have hzP : z ∈ P.toLocalProjectiveDevelopingMap.domain := by
    simpa [CenteredNormalizedSchwarzianFrobeniusPair.toLocalProjectiveDevelopingMap,
      CenteredNormalizedSchwarzianFrobeniusPair.toLocalSchwarzianODEChart,
      LocalSchwarzianODEChart.toLocalProjectiveDevelopingMap] using
      mem_centeredBallDomain_center P.radius_pos
  rcases hyperbolicSchwarzianBaseJetExistenceTheorem hu
      (P.toLocalProjectiveDevelopingMap.domain_subset hzP) with ⟨J⟩
  rcases hNorm P hzP J with ⟨N, _hNJ, hNz⟩
  exact ⟨S, a, P, N, hNz⟩

/--
Holomorphic Schwarzian data, Frobenius existence, and the explicit normal-form
derivative-identification boundary give Frobenius two-jet normalizations.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_derivativeIdentification
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hDeriv : LocalProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem) :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem :=
  hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_normalFormLift
    hS hFrob
    (localProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem_of_derivativeIdentification
      hDeriv)

/--
Holomorphic Schwarzian data, Frobenius existence, and the canonical
third-derivative normal-form package give Frobenius two-jet normalizations.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_canonicalThirdDerivativeIdentification
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hThird :
      LocalProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem) :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem :=
  hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_normalFormNormalization
    hS hFrob
    (localProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem_of_canonicalThirdDerivativeIdentification
      hThird)

/--
Holomorphic Schwarzian data, Frobenius existence, and the actual derivative of
the Frobenius ratio give Frobenius two-jet normalizations.  The normal-form
postcomposition derivative is now handled by the proved chain-rule bridge.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_affineHasDerivAt
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem)
    (hBase : LocalProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem) :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem :=
  hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_derivativeIdentification
    hS hFrob
    (localProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem_of_affineHasDerivAt
      hBase)

/--
Holomorphic Schwarzian data and Frobenius existence now give the normalized
Frobenius two-jet branches through the proved normal-form and quotient-rule
pipeline.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_provedNormalForm
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem :=
  hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem_of_canonicalThirdDerivativeIdentification
    hS hFrob
    localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem

/--
Frobenius two-jet normalizations together with the canonical pullback
derivative-identification data for the normalization that is actually
constructed.
-/
def HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsDerivativeIdentificationTheorem :
    Prop :=
  ∀ (u : LocalConformalFactor) ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ u.coordinateDomain →
      ∃ (S : LocalSchwarzianData u) (a : ℕ → ℂ)
        (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z a)
        (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization
          P.toLocalProjectiveDevelopingMap z),
        z ∈ N.domain ∧
          Nonempty (LocalHyperbolicCanonicalPullbackDerivativeIdentificationData N)

/--
Frobenius two-jet normalizations together with the canonical pullback
regularity data for the normalization that is actually constructed.
-/
def HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsRegularityTheorem :
    Prop :=
  ∀ (u : LocalConformalFactor) ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ u.coordinateDomain →
      ∃ (S : LocalSchwarzianData u) (a : ℕ → ℂ)
        (P : CenteredNormalizedSchwarzianFrobeniusPair
          S.coefficient u.coordinateDomain z a)
        (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization
          P.toLocalProjectiveDevelopingMap z),
        z ∈ N.domain ∧
          Nonempty (LocalHyperbolicCanonicalPullbackRegularityData N)

/--
Frobenius two-jet normalizations together with the bundled canonical pullback
derivative-algebra data for the normalization that is actually constructed.
-/
def HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem :
    Prop :=
  ∀ (u : LocalConformalFactor) ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ u.coordinateDomain →
      ∃ (S : LocalSchwarzianData u) (a : ℕ → ℂ)
        (P : CenteredNormalizedSchwarzianFrobeniusPair
          S.coefficient u.coordinateDomain z a)
        (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization
          P.toLocalProjectiveDevelopingMap z),
        z ∈ N.domain ∧
          Nonempty (LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N)

/--
Fixed-coefficient version of the Frobenius derivative-algebra construction.
This keeps a chosen Schwarzian datum attached to the constructed branch, which
is needed when the datum also carries the original metric-Schwarzian
identification.
-/
theorem localSchwarzianDataProducesFrobeniusTwoJetNormalizationsDerivativeAlgebra
    {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z : ℂ⦄
    (hu : u.SolvesLiouvilleEquation) (hz : z ∈ u.coordinateDomain)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
      ∃ (a : ℕ → ℂ)
        (P : CenteredNormalizedSchwarzianFrobeniusPair
          S.coefficient u.coordinateDomain z a)
        (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization
          P.toLocalProjectiveDevelopingMap z),
        z ∈ N.domain ∧
          Nonempty (LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N) := by
  rcases hFrob S hz with ⟨a, ⟨P⟩⟩
  have hzP : z ∈ P.toLocalProjectiveDevelopingMap.domain := by
    simpa [CenteredNormalizedSchwarzianFrobeniusPair.toLocalProjectiveDevelopingMap,
      CenteredNormalizedSchwarzianFrobeniusPair.toLocalSchwarzianODEChart,
      LocalSchwarzianODEChart.toLocalProjectiveDevelopingMap] using
      mem_centeredBallDomain_center P.radius_pos
  rcases hyperbolicSchwarzianBaseJetExistenceTheorem hu
      (P.toLocalProjectiveDevelopingMap.domain_subset hzP) with ⟨J⟩
  rcases localProjectiveFrobeniusNormalFormCanonicalLandingTheorem P hzP J with
    ⟨E, r, hr_pos, hsubset, hmaps, hthird⟩
  rcases localProjectiveFrobeniusNormalFormThirdDerivativeIdentificationTheorem
      P hzP J E r hr_pos hsubset hmaps hthird with
    ⟨A⟩
  let L : LocalProjectiveNormalFormUpperHalfPlaneLiftData E r :=
    E.liftDataOfDerivativeIdentification hmaps A.toDerivativeIdentificationData
  let N := L.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization hr_pos hsubset
  have hOrigCont :
      ContDiffOn ℝ 3 P.toLocalProjectiveDevelopingMap.affineMap E.domain :=
    P.toLocalProjectiveDevelopingMap_affineMap_contDiffOn.mono
      E.domain_subset_original
  have hOrigCont' :
      ContDiffOn ℝ 3
        (fun w : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv w)
        E.domain :=
    P.toLocalProjectiveDevelopingMap_affineMapDeriv_contDiffOn.mono
      E.domain_subset_original
  have hECont :
      ContDiffOn ℝ 3 E.toLocalProjectiveDevelopingMap.affineMap
        E.domain :=
    E.affineMap_contDiffOn_of_original hOrigCont
  have hEContBall :
      ContDiffOn ℝ 3 E.toLocalProjectiveDevelopingMap.affineMap
        (Metric.ball z r) :=
    hECont.mono hsubset
  have hUpper :
      ContDiffOn ℝ 3
        (fun w : ℂ ↦ (E.upperHalfPlaneMapOfLanding r hmaps w : ℂ))
        (Metric.ball z r) :=
    E.upperHalfPlaneMapOfLanding_contDiffOn_of_affineMap_contDiffOn
      hmaps hEContBall
  have hECont' :
      ContDiffOn ℝ 3
        (fun w : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv w)
        E.domain :=
    E.affineMapDeriv_contDiffOn_of_original hOrigCont hOrigCont'
  have hECont'Ball :
      ContDiffOn ℝ 3
        (fun w : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv w)
        (Metric.ball z r) :=
    hECont'.mono hsubset
  let R : LocalHyperbolicCanonicalPullbackRegularityData N := {
    upperHalfPlaneMap_contDiffOn := by
      simpa [N, L,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.liftDataOfDerivativeIdentification]
        using hUpper
    affineMapDeriv_contDiffOn := by
      simpa [N, L,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall]
        using hECont'Ball
    twice_differentiable_on_domain := by
      exact (N.pullbackLogDensity_contDiffOn_of_branch_contDiffOn
        (by
          simpa [N, L,
            LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
            LocalUpperHalfPlaneProjectiveNormalization.domain,
            LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
            LocalProjectiveNormalFormPostcompositionExplicitData.liftDataOfDerivativeIdentification]
            using hUpper)
        (by
          simpa [N, L,
            LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
            LocalUpperHalfPlaneProjectiveNormalization.domain,
            LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
            LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall]
            using hECont'Ball)).of_le (by norm_num)
  }
  let I : LocalHyperbolicCanonicalPullbackDerivativeIdentificationData N := {
    affineMap_differentiableAt := by
      intro w hw
      have hwBall : w ∈ Metric.ball z r := by
        simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
          LocalUpperHalfPlaneProjectiveNormalization.domain,
          LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
          using hw
      have hwE : w ∈ E.domain := hsubset hwBall
      have hOrig :
          HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
            (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hE :
          HasDerivAt E.toLocalProjectiveDevelopingMap.affineMap
            (E.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        E.affineMap_hasDerivAt_of_original hwE hOrig
      simpa [N, L,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
        hE.differentiableAt
    affineMap_deriv_eq := by
      intro w hw
      have hwBall : w ∈ Metric.ball z r := by
        simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
          LocalUpperHalfPlaneProjectiveNormalization.domain,
          LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
          using hw
      have hwE : w ∈ E.domain := hsubset hwBall
      have hOrig :
          HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
            (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hE :
          HasDerivAt E.toLocalProjectiveDevelopingMap.affineMap
            (E.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        E.affineMap_hasDerivAt_of_original hwE hOrig
      simpa [N, L,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
        hE.deriv
    affineMapDeriv_differentiableAt := by
      intro w hw
      have hwBall : w ∈ Metric.ball z r := by
        simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
          LocalUpperHalfPlaneProjectiveNormalization.domain,
          LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
          using hw
      have hwE : w ∈ E.domain := hsubset hwBall
      have hOrig :
          HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
            (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hOrig' :
          HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv t)
            (P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hE :
          HasDerivAt (fun t : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv t)
            (E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
        E.affineMapDeriv_hasDerivAt_of_original hwE hOrig hOrig'
      simpa [N, L,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
        hE.differentiableAt
    affineMapDeriv_deriv_eq := by
      intro w hw
      have hwBall : w ∈ Metric.ball z r := by
        simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
          LocalUpperHalfPlaneProjectiveNormalization.domain,
          LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
          using hw
      have hwE : w ∈ E.domain := hsubset hwBall
      have hOrig :
          HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
            (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hOrig' :
          HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv t)
            (P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hE :
          HasDerivAt (fun t : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv t)
            (E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
        E.affineMapDeriv_hasDerivAt_of_original hwE hOrig hOrig'
      simpa [N, L,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
        hE.deriv
    affineMapSecondDeriv_differentiableAt := by
      intro w hw
      have hwBall : w ∈ Metric.ball z r := by
        simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
          LocalUpperHalfPlaneProjectiveNormalization.domain,
          LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
          using hw
      have hwE : w ∈ E.domain := hsubset hwBall
      have hOrig :
          HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
            (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hOrig' :
          HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv t)
            (P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hOrig'' :
          HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv t)
            (P.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hE :
          HasDerivAt (fun t : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv t)
            (E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w) w :=
        E.affineMapSecondDeriv_hasDerivAt_of_original hwE
          hOrig hOrig' hOrig'' (hthird w hwBall)
      simpa [N, L,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
        hE.differentiableAt
    affineMapSecondDeriv_deriv_eq := by
      intro w hw
      have hwBall : w ∈ Metric.ball z r := by
        simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
          LocalUpperHalfPlaneProjectiveNormalization.domain,
          LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
          using hw
      have hwE : w ∈ E.domain := hsubset hwBall
      have hOrig :
          HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
            (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hOrig' :
          HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv t)
            (P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hOrig'' :
          HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv t)
            (P.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hE :
          HasDerivAt (fun t : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv t)
            (E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w) w :=
        E.affineMapSecondDeriv_hasDerivAt_of_original hwE
          hOrig hOrig' hOrig'' (hthird w hwBall)
      simpa [N, L,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
        hE.deriv
  }
  exact ⟨a, P, N, N.base_mem, ⟨R.withDerivativeIdentification I⟩⟩

/--
The proved Frobenius normal-form construction gives not only the two-jet
normalization, but also the canonical pullback derivative-identification data
for the constructed branch.  The remaining pullback-side analytic input is
therefore the regularity/smoothness package, not the ordinary derivative-value
identifications.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsDerivativeIdentificationTheorem
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsDerivativeIdentificationTheorem := by
  intro u z hu hz
  rcases hS u hu with ⟨S⟩
  rcases hFrob S hz with ⟨a, ⟨P⟩⟩
  have hzP : z ∈ P.toLocalProjectiveDevelopingMap.domain := by
    simpa [CenteredNormalizedSchwarzianFrobeniusPair.toLocalProjectiveDevelopingMap,
      CenteredNormalizedSchwarzianFrobeniusPair.toLocalSchwarzianODEChart,
      LocalSchwarzianODEChart.toLocalProjectiveDevelopingMap] using
      mem_centeredBallDomain_center P.radius_pos
  rcases hyperbolicSchwarzianBaseJetExistenceTheorem hu
      (P.toLocalProjectiveDevelopingMap.domain_subset hzP) with ⟨J⟩
  rcases localProjectiveFrobeniusNormalFormCanonicalLandingTheorem P hzP J with
    ⟨E, r, hr_pos, hsubset, hmaps, hthird⟩
  rcases localProjectiveFrobeniusNormalFormThirdDerivativeIdentificationTheorem
      P hzP J E r hr_pos hsubset hmaps hthird with
    ⟨A⟩
  let L : LocalProjectiveNormalFormUpperHalfPlaneLiftData E r :=
    E.liftDataOfDerivativeIdentification hmaps A.toDerivativeIdentificationData
  let N := L.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization hr_pos hsubset
  refine ⟨S, a, P, N, N.base_mem, ⟨?_⟩⟩
  refine {
    affineMap_differentiableAt := ?_
    affineMap_deriv_eq := ?_
    affineMapDeriv_differentiableAt := ?_
    affineMapDeriv_deriv_eq := ?_
    affineMapSecondDeriv_differentiableAt := ?_
    affineMapSecondDeriv_deriv_eq := ?_
  }
  · intro w hw
    have hwBall : w ∈ Metric.ball z r := by
      simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
        using hw
    have hwE : w ∈ E.domain := hsubset hwBall
    have hOrig :
        HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
          (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
      localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
        (E.domain_subset_original hwE)
    have hE :
        HasDerivAt E.toLocalProjectiveDevelopingMap.affineMap
          (E.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
      E.affineMap_hasDerivAt_of_original hwE hOrig
    simpa [N, L,
      LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
      LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
      hE.differentiableAt
  · intro w hw
    have hwBall : w ∈ Metric.ball z r := by
      simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
        using hw
    have hwE : w ∈ E.domain := hsubset hwBall
    have hOrig :
        HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
          (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
      localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
        (E.domain_subset_original hwE)
    have hE :
        HasDerivAt E.toLocalProjectiveDevelopingMap.affineMap
          (E.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
      E.affineMap_hasDerivAt_of_original hwE hOrig
    simpa [N, L,
      LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
      LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
      hE.deriv
  · intro w hw
    have hwBall : w ∈ Metric.ball z r := by
      simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
        using hw
    have hwE : w ∈ E.domain := hsubset hwBall
    have hOrig :
        HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
          (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
      localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
        (E.domain_subset_original hwE)
    have hOrig' :
        HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv t)
          (P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
      localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem P
        (E.domain_subset_original hwE)
    have hE :
        HasDerivAt (fun t : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv t)
          (E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
      E.affineMapDeriv_hasDerivAt_of_original hwE hOrig hOrig'
    simpa [N, L,
      LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
      LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
      hE.differentiableAt
  · intro w hw
    have hwBall : w ∈ Metric.ball z r := by
      simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
        using hw
    have hwE : w ∈ E.domain := hsubset hwBall
    have hOrig :
        HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
          (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
      localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
        (E.domain_subset_original hwE)
    have hOrig' :
        HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv t)
          (P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
      localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem P
        (E.domain_subset_original hwE)
    have hE :
        HasDerivAt (fun t : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv t)
          (E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
      E.affineMapDeriv_hasDerivAt_of_original hwE hOrig hOrig'
    simpa [N, L,
      LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
      LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
      hE.deriv
  · intro w hw
    have hwBall : w ∈ Metric.ball z r := by
      simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
        using hw
    have hwE : w ∈ E.domain := hsubset hwBall
    have hOrig :
        HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
          (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
      localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
        (E.domain_subset_original hwE)
    have hOrig' :
        HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv t)
          (P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
      localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem P
        (E.domain_subset_original hwE)
    have hOrig'' :
        HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv t)
          (P.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w) w :=
      localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem P
        (E.domain_subset_original hwE)
    have hE :
        HasDerivAt (fun t : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv t)
          (E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w) w :=
      E.affineMapSecondDeriv_hasDerivAt_of_original hwE
        hOrig hOrig' hOrig'' (hthird w hwBall)
    simpa [N, L,
      LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
      LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
      hE.differentiableAt
  · intro w hw
    have hwBall : w ∈ Metric.ball z r := by
      simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
        using hw
    have hwE : w ∈ E.domain := hsubset hwBall
    have hOrig :
        HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
          (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
      localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
        (E.domain_subset_original hwE)
    have hOrig' :
        HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv t)
          (P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
      localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem P
        (E.domain_subset_original hwE)
    have hOrig'' :
        HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv t)
          (P.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w) w :=
      localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem P
        (E.domain_subset_original hwE)
    have hE :
        HasDerivAt (fun t : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv t)
          (E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w) w :=
      E.affineMapSecondDeriv_hasDerivAt_of_original hwE
        hOrig hOrig' hOrig'' (hthird w hwBall)
    simpa [N, L,
      LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
      LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
      hE.deriv

/--
With the proved holomorphic-Schwarzian and local analytic Frobenius inputs,
the constructed Frobenius normalizations carry derivative-identification data.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsDerivativeIdentificationTheorem_proved :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsDerivativeIdentificationTheorem :=
  hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsDerivativeIdentificationTheorem
    hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
    holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic

/--
The Frobenius normal-form construction also supplies the regularity side of
the canonical pullback package for the constructed normalized branch.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsRegularityTheorem
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsRegularityTheorem := by
  intro u z hu hz
  rcases hS u hu with ⟨S⟩
  rcases hFrob S hz with ⟨a, ⟨P⟩⟩
  have hzP : z ∈ P.toLocalProjectiveDevelopingMap.domain := by
    simpa [CenteredNormalizedSchwarzianFrobeniusPair.toLocalProjectiveDevelopingMap,
      CenteredNormalizedSchwarzianFrobeniusPair.toLocalSchwarzianODEChart,
      LocalSchwarzianODEChart.toLocalProjectiveDevelopingMap] using
      mem_centeredBallDomain_center P.radius_pos
  rcases hyperbolicSchwarzianBaseJetExistenceTheorem hu
      (P.toLocalProjectiveDevelopingMap.domain_subset hzP) with ⟨J⟩
  rcases localProjectiveFrobeniusNormalFormCanonicalLandingTheorem P hzP J with
    ⟨E, r, hr_pos, hsubset, hmaps, hthird⟩
  rcases localProjectiveFrobeniusNormalFormThirdDerivativeIdentificationTheorem
      P hzP J E r hr_pos hsubset hmaps hthird with
    ⟨A⟩
  let L : LocalProjectiveNormalFormUpperHalfPlaneLiftData E r :=
    E.liftDataOfDerivativeIdentification hmaps A.toDerivativeIdentificationData
  let N := L.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization hr_pos hsubset
  have hOrig :
      ContDiffOn ℝ 3 P.toLocalProjectiveDevelopingMap.affineMap E.domain :=
    P.toLocalProjectiveDevelopingMap_affineMap_contDiffOn.mono
      E.domain_subset_original
  have hOrig' :
      ContDiffOn ℝ 3
        (fun w : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv w)
        E.domain :=
    P.toLocalProjectiveDevelopingMap_affineMapDeriv_contDiffOn.mono
      E.domain_subset_original
  have hE :
      ContDiffOn ℝ 3 E.toLocalProjectiveDevelopingMap.affineMap
        E.domain :=
    E.affineMap_contDiffOn_of_original hOrig
  have hEBall :
      ContDiffOn ℝ 3 E.toLocalProjectiveDevelopingMap.affineMap
        (Metric.ball z r) :=
    hE.mono hsubset
  have hUpper :
      ContDiffOn ℝ 3
        (fun w : ℂ ↦ (E.upperHalfPlaneMapOfLanding r hmaps w : ℂ))
        (Metric.ball z r) :=
    E.upperHalfPlaneMapOfLanding_contDiffOn_of_affineMap_contDiffOn hmaps hEBall
  have hE' :
      ContDiffOn ℝ 3
        (fun w : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv w)
        E.domain :=
    E.affineMapDeriv_contDiffOn_of_original hOrig hOrig'
  have hE'Ball :
      ContDiffOn ℝ 3
        (fun w : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv w)
        (Metric.ball z r) :=
    hE'.mono hsubset
  refine ⟨S, a, P, N, N.base_mem, ⟨?_⟩⟩
  refine {
    upperHalfPlaneMap_contDiffOn := ?_
    affineMapDeriv_contDiffOn := ?_
    twice_differentiable_on_domain := by
      exact (N.pullbackLogDensity_contDiffOn_of_branch_contDiffOn
        (by
          simpa [N, L,
            LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
            LocalUpperHalfPlaneProjectiveNormalization.domain,
            LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
            LocalProjectiveNormalFormPostcompositionExplicitData.liftDataOfDerivativeIdentification]
            using hUpper)
        (by
          simpa [N, L,
            LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
            LocalUpperHalfPlaneProjectiveNormalization.domain,
            LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
            LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall]
            using hE'Ball)).of_le (by norm_num)
  }
  · simpa [N, L,
      LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
      LocalUpperHalfPlaneProjectiveNormalization.domain,
      LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
      LocalProjectiveNormalFormPostcompositionExplicitData.liftDataOfDerivativeIdentification]
      using hUpper
  · simpa [N, L,
      LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
      LocalUpperHalfPlaneProjectiveNormalization.domain,
      LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
      LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall]
      using hE'Ball

/--
With the proved holomorphic-Schwarzian and local analytic Frobenius inputs,
the constructed Frobenius normalizations carry canonical pullback regularity
data.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsRegularityTheorem_proved :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsRegularityTheorem :=
  hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsRegularityTheorem
    hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
    holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic

/--
For the actual branch produced by the Frobenius normal-form construction, the
regularity and derivative-identification packages are available
simultaneously, hence combine to canonical pullback derivative algebra.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem
    (hS : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem := by
  intro u z hu hz
  rcases hS u hu with ⟨S⟩
  rcases hFrob S hz with ⟨a, ⟨P⟩⟩
  have hzP : z ∈ P.toLocalProjectiveDevelopingMap.domain := by
    simpa [CenteredNormalizedSchwarzianFrobeniusPair.toLocalProjectiveDevelopingMap,
      CenteredNormalizedSchwarzianFrobeniusPair.toLocalSchwarzianODEChart,
      LocalSchwarzianODEChart.toLocalProjectiveDevelopingMap] using
      mem_centeredBallDomain_center P.radius_pos
  rcases hyperbolicSchwarzianBaseJetExistenceTheorem hu
      (P.toLocalProjectiveDevelopingMap.domain_subset hzP) with ⟨J⟩
  rcases localProjectiveFrobeniusNormalFormCanonicalLandingTheorem P hzP J with
    ⟨E, r, hr_pos, hsubset, hmaps, hthird⟩
  rcases localProjectiveFrobeniusNormalFormThirdDerivativeIdentificationTheorem
      P hzP J E r hr_pos hsubset hmaps hthird with
    ⟨A⟩
  let L : LocalProjectiveNormalFormUpperHalfPlaneLiftData E r :=
    E.liftDataOfDerivativeIdentification hmaps A.toDerivativeIdentificationData
  let N := L.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization hr_pos hsubset
  have hOrigCont :
      ContDiffOn ℝ 3 P.toLocalProjectiveDevelopingMap.affineMap E.domain :=
    P.toLocalProjectiveDevelopingMap_affineMap_contDiffOn.mono
      E.domain_subset_original
  have hOrigCont' :
      ContDiffOn ℝ 3
        (fun w : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv w)
        E.domain :=
    P.toLocalProjectiveDevelopingMap_affineMapDeriv_contDiffOn.mono
      E.domain_subset_original
  have hECont :
      ContDiffOn ℝ 3 E.toLocalProjectiveDevelopingMap.affineMap
        E.domain :=
    E.affineMap_contDiffOn_of_original hOrigCont
  have hEContBall :
      ContDiffOn ℝ 3 E.toLocalProjectiveDevelopingMap.affineMap
        (Metric.ball z r) :=
    hECont.mono hsubset
  have hUpper :
      ContDiffOn ℝ 3
        (fun w : ℂ ↦ (E.upperHalfPlaneMapOfLanding r hmaps w : ℂ))
        (Metric.ball z r) :=
    E.upperHalfPlaneMapOfLanding_contDiffOn_of_affineMap_contDiffOn
      hmaps hEContBall
  have hECont' :
      ContDiffOn ℝ 3
        (fun w : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv w)
        E.domain :=
    E.affineMapDeriv_contDiffOn_of_original hOrigCont hOrigCont'
  have hECont'Ball :
      ContDiffOn ℝ 3
        (fun w : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv w)
        (Metric.ball z r) :=
    hECont'.mono hsubset
  let R : LocalHyperbolicCanonicalPullbackRegularityData N := {
    upperHalfPlaneMap_contDiffOn := by
      simpa [N, L,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.liftDataOfDerivativeIdentification]
        using hUpper
    affineMapDeriv_contDiffOn := by
      simpa [N, L,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall]
        using hECont'Ball
    twice_differentiable_on_domain := by
      exact (N.pullbackLogDensity_contDiffOn_of_branch_contDiffOn
        (by
          simpa [N, L,
            LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
            LocalUpperHalfPlaneProjectiveNormalization.domain,
            LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
            LocalProjectiveNormalFormPostcompositionExplicitData.liftDataOfDerivativeIdentification]
            using hUpper)
        (by
          simpa [N, L,
            LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
            LocalUpperHalfPlaneProjectiveNormalization.domain,
            LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
            LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall]
            using hECont'Ball)).of_le (by norm_num)
  }
  let I : LocalHyperbolicCanonicalPullbackDerivativeIdentificationData N := {
    affineMap_differentiableAt := by
      intro w hw
      have hwBall : w ∈ Metric.ball z r := by
        simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
          LocalUpperHalfPlaneProjectiveNormalization.domain,
          LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
          using hw
      have hwE : w ∈ E.domain := hsubset hwBall
      have hOrig :
          HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
            (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hE :
          HasDerivAt E.toLocalProjectiveDevelopingMap.affineMap
            (E.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        E.affineMap_hasDerivAt_of_original hwE hOrig
      simpa [N, L,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
        hE.differentiableAt
    affineMap_deriv_eq := by
      intro w hw
      have hwBall : w ∈ Metric.ball z r := by
        simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
          LocalUpperHalfPlaneProjectiveNormalization.domain,
          LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
          using hw
      have hwE : w ∈ E.domain := hsubset hwBall
      have hOrig :
          HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
            (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hE :
          HasDerivAt E.toLocalProjectiveDevelopingMap.affineMap
            (E.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        E.affineMap_hasDerivAt_of_original hwE hOrig
      simpa [N, L,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
        hE.deriv
    affineMapDeriv_differentiableAt := by
      intro w hw
      have hwBall : w ∈ Metric.ball z r := by
        simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
          LocalUpperHalfPlaneProjectiveNormalization.domain,
          LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
          using hw
      have hwE : w ∈ E.domain := hsubset hwBall
      have hOrig :
          HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
            (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hOrig' :
          HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv t)
            (P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hE :
          HasDerivAt (fun t : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv t)
            (E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
        E.affineMapDeriv_hasDerivAt_of_original hwE hOrig hOrig'
      simpa [N, L,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
        hE.differentiableAt
    affineMapDeriv_deriv_eq := by
      intro w hw
      have hwBall : w ∈ Metric.ball z r := by
        simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
          LocalUpperHalfPlaneProjectiveNormalization.domain,
          LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
          using hw
      have hwE : w ∈ E.domain := hsubset hwBall
      have hOrig :
          HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
            (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hOrig' :
          HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv t)
            (P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hE :
          HasDerivAt (fun t : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapDeriv t)
            (E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
        E.affineMapDeriv_hasDerivAt_of_original hwE hOrig hOrig'
      simpa [N, L,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
        hE.deriv
    affineMapSecondDeriv_differentiableAt := by
      intro w hw
      have hwBall : w ∈ Metric.ball z r := by
        simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
          LocalUpperHalfPlaneProjectiveNormalization.domain,
          LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
          using hw
      have hwE : w ∈ E.domain := hsubset hwBall
      have hOrig :
          HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
            (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hOrig' :
          HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv t)
            (P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hOrig'' :
          HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv t)
            (P.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hE :
          HasDerivAt (fun t : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv t)
            (E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w) w :=
        E.affineMapSecondDeriv_hasDerivAt_of_original hwE
          hOrig hOrig' hOrig'' (hthird w hwBall)
      simpa [N, L,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
        hE.differentiableAt
    affineMapSecondDeriv_deriv_eq := by
      intro w hw
      have hwBall : w ∈ Metric.ball z r := by
        simpa [N, L, LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain,
          LocalUpperHalfPlaneProjectiveNormalization.domain,
          LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization]
          using hw
      have hwE : w ∈ E.domain := hsubset hwBall
      have hOrig :
          HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
            (P.toLocalProjectiveDevelopingMap.affineMapDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hOrig' :
          HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv t)
            (P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hOrig'' :
          HasDerivAt (fun t : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv t)
            (P.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w) w :=
        localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem P
          (E.domain_subset_original hwE)
      have hE :
          HasDerivAt (fun t : ℂ ↦ E.toLocalProjectiveDevelopingMap.affineMapSecondDeriv t)
            (E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w) w :=
        E.affineMapSecondDeriv_hasDerivAt_of_original hwE
          hOrig hOrig' hOrig'' (hthird w hwBall)
      simpa [N, L,
        LocalProjectiveNormalFormUpperHalfPlaneLiftData.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization,
        LocalProjectiveNormalFormPostcompositionExplicitData.restrictToBall] using
        hE.deriv
  }
  refine ⟨S, a, P, N, N.base_mem, ⟨?_⟩⟩
  exact R.withDerivativeIdentification I

/--
With the proved holomorphic-Schwarzian and local analytic Frobenius inputs,
the constructed Frobenius normalizations carry bundled derivative algebra.
-/
theorem hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem_proved :
    HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem :=
  hyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem
    hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
    holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic

/--
Metric-Schwarzian Frobenius two-jet normalizations with derivative algebra
for the branch constructed from the actual metric Schwarzian coefficient.
-/
def HyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem :
    Prop :=
  ∀ (u : LocalConformalFactor) ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ u.coordinateDomain →
      ∃ (M : LocalMetricSchwarzianData u) (a : ℕ → ℂ)
        (P : CenteredNormalizedSchwarzianFrobeniusPair
          M.toLocalSchwarzianData.coefficient u.coordinateDomain z a)
        (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization
          P.toLocalProjectiveDevelopingMap z),
        z ∈ N.domain ∧
          Nonempty (LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N)

/--
Metric-Schwarzian data and Frobenius existence construct the normalized
Frobenius branch and keep the original metric-Schwarzian identification
attached to it.
-/
theorem hyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem
    (hMetric : HyperbolicLiouvilleProducesMetricSchwarzianDataTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    HyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem := by
  intro u z hu hz
  rcases hMetric u hu with ⟨M⟩
  rcases localSchwarzianDataProducesFrobeniusTwoJetNormalizationsDerivativeAlgebra
      M.toLocalSchwarzianData hu hz hFrob with
    ⟨a, P, N, hNz, hAlg⟩
  exact ⟨M, a, P, N, hNz, hAlg⟩

/--
With the proved metric-Schwarzian and local analytic Frobenius inputs, the
constructed metric-Schwarzian Frobenius normalizations carry bundled
derivative algebra.
-/
theorem hyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem_proved :
    HyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem :=
  hyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem
    hyperbolicLiouvilleProducesMetricSchwarzianDataTheorem
    holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic

/--
The metric-Schwarzian Frobenius derivative-algebra construction directly gives
local upper-half-plane developing maps with the original Poincare pullback
metric formula.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra
    (hMetricAlg :
      HyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem := by
  intro u z hu hz
  rcases hMetricAlg u hu hz with ⟨M, _a, _P, N, hNz, ⟨A⟩⟩
  exact ⟨M.toLocalSchwarzianData,
    N.normalized.toLocalUpperHalfPlaneDevelopingMap
      (A.metric_recovery_of_originalMetricSchwarzian
        hu M.originalMetricIdentification), hNz⟩

/--
The local upper-half-plane developing-map theorem now follows from the proved
metric-Schwarzian, Frobenius, normal-form, and derivative-algebra packages.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_proved :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra
    hyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem_proved

/--
Public closed form of the local upper-half-plane developing-map theorem.
-/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_proved

/--
Metric-aware local upper-half-plane developing-map theorem.

The older theorem forgets the metric-Schwarzian data after constructing the
branch.  This version retains the coefficient provenance, which is the data
used by overlap coefficient agreement.
-/
def HyperbolicLiouvilleProducesLocalMetricSchwarzianUpperHalfPlaneDevelopingMapsTheorem :
    Prop :=
  ∀ (u : LocalConformalFactor) ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ u.coordinateDomain →
      ∃ (M : LocalMetricSchwarzianData u)
        (H : LocalUpperHalfPlaneDevelopingMap M.toLocalSchwarzianData),
          z ∈ H.domain

/-- Forgetting metric-Schwarzian provenance recovers the older upper-half-plane target. -/
theorem hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzianUpperHalfPlane
    (h :
      HyperbolicLiouvilleProducesLocalMetricSchwarzianUpperHalfPlaneDevelopingMapsTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem := by
  intro u z hu hz
  rcases h u (z := z) hu hz with ⟨M, H, hHz⟩
  exact ⟨M.toLocalSchwarzianData, H, hHz⟩

/--
The metric-Schwarzian Frobenius derivative-algebra construction directly gives
metric-aware local upper-half-plane developing maps.
-/
theorem hyperbolicLiouvilleProducesLocalMetricSchwarzianUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra
    (hMetricAlg :
      HyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem) :
    HyperbolicLiouvilleProducesLocalMetricSchwarzianUpperHalfPlaneDevelopingMapsTheorem := by
  intro u z hu hz
  rcases hMetricAlg u hu hz with ⟨M, _a, _P, N, hNz, ⟨A⟩⟩
  exact ⟨M,
    N.normalized.toLocalUpperHalfPlaneDevelopingMap
      (A.metric_recovery_of_originalMetricSchwarzian
        hu M.originalMetricIdentification), hNz⟩

/-- Public metric-aware closed form of the local upper-half-plane theorem. -/
theorem hyperbolicLiouvilleProducesLocalMetricSchwarzianUpperHalfPlaneDevelopingMapsTheorem :
    HyperbolicLiouvilleProducesLocalMetricSchwarzianUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalMetricSchwarzianUpperHalfPlaneDevelopingMapsTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra
    hyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem_proved

/-- Metric-aware local upper-half-plane branches project to metric-aware projective maps. -/
theorem hyperbolicLiouvilleProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem_of_upperHalfPlane
    (h :
      HyperbolicLiouvilleProducesLocalMetricSchwarzianUpperHalfPlaneDevelopingMapsTheorem) :
    HyperbolicLiouvilleProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem := by
  intro u z hu hz
  rcases h u (z := z) hu hz with ⟨M, H, hHz⟩
  exact ⟨M, H.toLocalProjectiveDevelopingMap, hHz⟩

/-- Public closed form of the metric-aware local projective developing-map theorem. -/
theorem hyperbolicLiouvilleProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem :
    HyperbolicLiouvilleProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem_of_upperHalfPlane
    hyperbolicLiouvilleProducesLocalMetricSchwarzianUpperHalfPlaneDevelopingMapsTheorem

/--
Public closed form of the local projective developing-map theorem.
-/
theorem hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_metricSchwarzian
    hyperbolicLiouvilleProducesLocalMetricSchwarzianProjectiveDevelopingMapsTheorem

/--
The metric-Schwarzian Frobenius derivative-algebra construction also gives a
coordinate-domain ball pre-atlas of metric-recovering normalized branches.
The ball domains are retained from the actual two-jet normalizations.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra
    (hMetricAlg :
      HyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem := by
  classical
  intro u hu
  let localMetricAlg :
      ∀ z : u.coordinateDomain,
        Σ' M : LocalMetricSchwarzianData u,
        Σ' a : ℕ → ℂ,
        Σ' P : CenteredNormalizedSchwarzianFrobeniusPair
          M.toLocalSchwarzianData.coefficient u.coordinateDomain (z : ℂ) a,
        Σ' N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization
          P.toLocalProjectiveDevelopingMap (z : ℂ),
          (z : ℂ) ∈ N.domain ∧
            Nonempty (LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N) :=
    fun z ↦
      let h :
          ∃ (M : LocalMetricSchwarzianData u) (a : ℕ → ℂ)
            (P : CenteredNormalizedSchwarzianFrobeniusPair
              M.toLocalSchwarzianData.coefficient u.coordinateDomain (z : ℂ) a)
            (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization
              P.toLocalProjectiveDevelopingMap (z : ℂ)),
            (z : ℂ) ∈ N.domain ∧
              Nonempty (LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N) :=
        hMetricAlg u hu z.property
      ⟨Classical.choose h,
        Classical.choose (Classical.choose_spec h),
        Classical.choose (Classical.choose_spec (Classical.choose_spec h)),
        Classical.choose
          (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))),
        Classical.choose_spec
          (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)))⟩
  let MAt : u.coordinateDomain → LocalMetricSchwarzianData u :=
    fun z ↦ (localMetricAlg z).1
  let SAt : u.coordinateDomain → LocalSchwarzianData u :=
    fun z ↦ (MAt z).toLocalSchwarzianData
  let PAt :
      ∀ z : u.coordinateDomain,
        CenteredNormalizedSchwarzianFrobeniusPair
          (SAt z).coefficient u.coordinateDomain (z : ℂ)
            ((localMetricAlg z).2.1) :=
    fun z ↦ (localMetricAlg z).2.2.1
  let DAt : ∀ z : u.coordinateDomain, LocalProjectiveDevelopingMap (SAt z) :=
    fun z ↦ (PAt z).toLocalProjectiveDevelopingMap
  let NAt :
      ∀ z : u.coordinateDomain,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization (DAt z) (z : ℂ) :=
    fun z ↦ (localMetricAlg z).2.2.2.1
  have hNAt : ∀ z : u.coordinateDomain, (z : ℂ) ∈ (NAt z).domain := by
    intro z
    exact (localMetricAlg z).2.2.2.2.1
  have hAlgAt :
      ∀ z : u.coordinateDomain,
        Nonempty (LocalHyperbolicCanonicalPullbackDerivativeAlgebraData (NAt z)) := by
    intro z
    exact (localMetricAlg z).2.2.2.2.2
  let normalizationAt :
      ∀ z : u.coordinateDomain,
        LocalMetricRecoveringUpperHalfPlaneNormalization (DAt z) :=
    fun z ↦
      LocalMetricRecoveringUpperHalfPlaneNormalization.ofTwoJetNormalization
        (NAt z) (by
          rcases hAlgAt z with ⟨A⟩
          exact A.metric_recovery_of_originalMetricSchwarzian
            hu (MAt z).originalMetricIdentification)
  refine ⟨{
    schwarzianAt := SAt
    projectiveAt := DAt
    normalizationAt := normalizationAt
    mem_normalized_domain := ?_
    ball_domain := ?_
  }⟩
  · intro z
    exact hNAt z
  · intro z
    rcases hyperbolicTwoJetNormalizationHasBallDomainTheorem
        (SAt z) (NAt z) with ⟨c, r, hdomain⟩
    exact ⟨c, r, by
      simpa [normalizationAt, LocalMetricRecoveringUpperHalfPlaneNormalization.ofTwoJetNormalization,
        LocalUpperHalfPlaneDevelopingMap.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain] using hdomain⟩

/--
The proved metric-Schwarzian Frobenius derivative-algebra construction gives
coordinate-domain metric-recovering normalization atlases with preconnected
overlaps, because the chosen branch domains are balls.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra_proved :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_ballPreAtlas
    (hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra
      hyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem_proved)

/--
Strengthened local output retaining the metric-Schwarzian data used to build
each branch of the normalization atlas.
-/
def HyperbolicLiouvilleProducesLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlasTheorem :
    Prop :=
  ∀ u : LocalConformalFactor,
    u.SolvesLiouvilleEquation →
      Nonempty (LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas u)

/--
Strengthened local output retaining both the metric-Schwarzian data and the
projective derivative algebra for the selected normalized branches.
-/
def HyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem :
    Prop :=
  ∀ u : LocalConformalFactor,
    u.SolvesLiouvilleEquation →
      Nonempty (LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u)

/--
The metric-Schwarzian Frobenius derivative-algebra construction gives the
strengthened normalization atlas that remembers the metric-Schwarzian
coefficient identifications.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra
    (hMetricAlg :
      HyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem) :
    HyperbolicLiouvilleProducesLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlasTheorem := by
  classical
  intro u hu
  let localMetricAlg :
      ∀ z : u.coordinateDomain,
        Σ' M : LocalMetricSchwarzianData u,
        Σ' a : ℕ → ℂ,
        Σ' P : CenteredNormalizedSchwarzianFrobeniusPair
          M.toLocalSchwarzianData.coefficient u.coordinateDomain (z : ℂ) a,
        Σ' N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization
          P.toLocalProjectiveDevelopingMap (z : ℂ),
          (z : ℂ) ∈ N.domain ∧
            Nonempty (LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N) :=
    fun z ↦
      let h :
          ∃ (M : LocalMetricSchwarzianData u) (a : ℕ → ℂ)
            (P : CenteredNormalizedSchwarzianFrobeniusPair
              M.toLocalSchwarzianData.coefficient u.coordinateDomain (z : ℂ) a)
            (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization
              P.toLocalProjectiveDevelopingMap (z : ℂ)),
            (z : ℂ) ∈ N.domain ∧
              Nonempty (LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N) :=
        hMetricAlg u hu z.property
      ⟨Classical.choose h,
        Classical.choose (Classical.choose_spec h),
        Classical.choose (Classical.choose_spec (Classical.choose_spec h)),
        Classical.choose
          (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))),
        Classical.choose_spec
          (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)))⟩
  let MAt : u.coordinateDomain → LocalMetricSchwarzianData u :=
    fun z ↦ (localMetricAlg z).1
  let SAt : u.coordinateDomain → LocalSchwarzianData u :=
    fun z ↦ (MAt z).toLocalSchwarzianData
  let PAt :
      ∀ z : u.coordinateDomain,
        CenteredNormalizedSchwarzianFrobeniusPair
          (SAt z).coefficient u.coordinateDomain (z : ℂ)
            ((localMetricAlg z).2.1) :=
    fun z ↦ (localMetricAlg z).2.2.1
  let DAt :
      ∀ z : u.coordinateDomain,
        LocalProjectiveDevelopingMap ((MAt z).toLocalSchwarzianData) :=
    fun z ↦ (PAt z).toLocalProjectiveDevelopingMap
  let NAt :
      ∀ z : u.coordinateDomain,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization (DAt z) (z : ℂ) :=
    fun z ↦ (localMetricAlg z).2.2.2.1
  have hNAt : ∀ z : u.coordinateDomain, (z : ℂ) ∈ (NAt z).domain := by
    intro z
    exact (localMetricAlg z).2.2.2.2.1
  have hAlgAt :
      ∀ z : u.coordinateDomain,
        Nonempty (LocalHyperbolicCanonicalPullbackDerivativeAlgebraData (NAt z)) := by
    intro z
    exact (localMetricAlg z).2.2.2.2.2
  let normalizationAt :
      ∀ z : u.coordinateDomain,
        LocalMetricRecoveringUpperHalfPlaneNormalization (DAt z) :=
    fun z ↦
      LocalMetricRecoveringUpperHalfPlaneNormalization.ofTwoJetNormalization
        (NAt z) (by
          rcases hAlgAt z with ⟨A⟩
          exact A.metric_recovery_of_originalMetricSchwarzian
            hu (MAt z).originalMetricIdentification)
  refine ⟨{
    metricSchwarzianAt := MAt
    projectiveAt := DAt
    normalizationAt := normalizationAt
    mem_normalized_domain := ?_
    overlap_preconnected := ?_
  }⟩
  · intro z
    exact hNAt z
  · intro z w
    rcases hyperbolicTwoJetNormalizationHasBallDomainTheorem
        (SAt z) (NAt z) with ⟨cz, rz, hz⟩
    rcases hyperbolicTwoJetNormalizationHasBallDomainTheorem
        (SAt w) (NAt w) with ⟨cw, rw, hw⟩
    rw [show (normalizationAt z).normalized.domain = Metric.ball cz rz by
      simpa [normalizationAt, LocalMetricRecoveringUpperHalfPlaneNormalization.ofTwoJetNormalization,
        LocalUpperHalfPlaneDevelopingMap.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain] using hz]
    rw [show (normalizationAt w).normalized.domain = Metric.ball cw rw by
      simpa [normalizationAt, LocalMetricRecoveringUpperHalfPlaneNormalization.ofTwoJetNormalization,
        LocalUpperHalfPlaneDevelopingMap.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain] using hw]
    exact ((convex_ball cz rz).inter (convex_ball cw rw)).isPreconnected

/--
The same metric-Schwarzian Frobenius construction gives the strengthened atlas
that remembers the projective derivative algebra of each selected normalized
branch.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra
    (hMetricAlg :
      HyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem) :
    HyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem := by
  classical
  intro u hu
  let localMetricAlg :
      ∀ z : u.coordinateDomain,
        Σ' M : LocalMetricSchwarzianData u,
        Σ' a : ℕ → ℂ,
        Σ' P : CenteredNormalizedSchwarzianFrobeniusPair
          M.toLocalSchwarzianData.coefficient u.coordinateDomain (z : ℂ) a,
        Σ' N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization
          P.toLocalProjectiveDevelopingMap (z : ℂ),
          (z : ℂ) ∈ N.domain ∧
            Nonempty (LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N) :=
    fun z ↦
      let h :
          ∃ (M : LocalMetricSchwarzianData u) (a : ℕ → ℂ)
            (P : CenteredNormalizedSchwarzianFrobeniusPair
              M.toLocalSchwarzianData.coefficient u.coordinateDomain (z : ℂ) a)
            (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization
              P.toLocalProjectiveDevelopingMap (z : ℂ)),
            (z : ℂ) ∈ N.domain ∧
              Nonempty (LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N) :=
        hMetricAlg u hu z.property
      ⟨Classical.choose h,
        Classical.choose (Classical.choose_spec h),
        Classical.choose (Classical.choose_spec (Classical.choose_spec h)),
        Classical.choose
          (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))),
        Classical.choose_spec
          (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)))⟩
  let MAt : u.coordinateDomain → LocalMetricSchwarzianData u :=
    fun z ↦ (localMetricAlg z).1
  let SAt : u.coordinateDomain → LocalSchwarzianData u :=
    fun z ↦ (MAt z).toLocalSchwarzianData
  let PAt :
      ∀ z : u.coordinateDomain,
        CenteredNormalizedSchwarzianFrobeniusPair
          (SAt z).coefficient u.coordinateDomain (z : ℂ)
            ((localMetricAlg z).2.1) :=
    fun z ↦ (localMetricAlg z).2.2.1
  let DAt :
      ∀ z : u.coordinateDomain,
        LocalProjectiveDevelopingMap ((MAt z).toLocalSchwarzianData) :=
    fun z ↦ (PAt z).toLocalProjectiveDevelopingMap
  let NAt :
      ∀ z : u.coordinateDomain,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization (DAt z) (z : ℂ) :=
    fun z ↦ (localMetricAlg z).2.2.2.1
  have hNAt : ∀ z : u.coordinateDomain, (z : ℂ) ∈ (NAt z).domain := by
    intro z
    exact (localMetricAlg z).2.2.2.2.1
  have hAlgAt :
      ∀ z : u.coordinateDomain,
        Nonempty (LocalHyperbolicCanonicalPullbackDerivativeAlgebraData (NAt z)) := by
    intro z
    exact (localMetricAlg z).2.2.2.2.2
  let normalizationAt :
      ∀ z : u.coordinateDomain,
        LocalMetricRecoveringUpperHalfPlaneNormalization (DAt z) :=
    fun z ↦
      LocalMetricRecoveringUpperHalfPlaneNormalization.ofTwoJetNormalization
        (NAt z) (by
          rcases hAlgAt z with ⟨A⟩
          exact A.metric_recovery_of_originalMetricSchwarzian
            hu (MAt z).originalMetricIdentification)
  refine ⟨{
    metricSchwarzianAt := MAt
    projectiveAt := DAt
    normalizationAt := normalizationAt
    mem_normalized_domain := ?_
    overlap_preconnected := ?_
    projectiveFirstDerivative_hasDerivAt := ?_
    projectiveSecondDerivative_hasDerivAt := ?_
  }⟩
  · intro z
    exact hNAt z
  · intro z w
    rcases hyperbolicTwoJetNormalizationHasBallDomainTheorem
        (SAt z) (NAt z) with ⟨cz, rz, hz⟩
    rcases hyperbolicTwoJetNormalizationHasBallDomainTheorem
        (SAt w) (NAt w) with ⟨cw, rw, hw⟩
    rw [show (normalizationAt z).normalized.domain = Metric.ball cz rz by
      simpa [normalizationAt, LocalMetricRecoveringUpperHalfPlaneNormalization.ofTwoJetNormalization,
        LocalUpperHalfPlaneDevelopingMap.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain] using hz]
    rw [show (normalizationAt w).normalized.domain = Metric.ball cw rw by
      simpa [normalizationAt, LocalMetricRecoveringUpperHalfPlaneNormalization.ofTwoJetNormalization,
        LocalUpperHalfPlaneDevelopingMap.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain] using hw]
    exact ((convex_ball cz rz).inter (convex_ball cw rw)).isPreconnected
  · intro z x hx
    rcases hAlgAt z with ⟨A⟩
    let B : LocalHyperbolicCanonicalPullbackAffineDerivativeAlgebraData (NAt z) :=
      A.toAffineDerivativeAlgebraData
    exact by
      simpa [normalizationAt, LocalMetricRecoveringUpperHalfPlaneNormalization.ofTwoJetNormalization,
        LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas.normalizedBranch,
        LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas.toMetricDataAtlas,
        LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.normalizedBranch,
        LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.schwarzianAt,
        LocalUpperHalfPlaneDevelopingMap.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain] using
        B.affineMapDeriv_hasDerivAt x hx
  · intro z x hx
    rcases hAlgAt z with ⟨A⟩
    let B : LocalHyperbolicCanonicalPullbackAffineDerivativeAlgebraData (NAt z) :=
      A.toAffineDerivativeAlgebraData
    exact by
      simpa [normalizationAt, LocalMetricRecoveringUpperHalfPlaneNormalization.ofTwoJetNormalization,
        LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas.normalizedBranch,
        LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas.toMetricDataAtlas,
        LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.normalizedBranch,
        LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.schwarzianAt,
        LocalUpperHalfPlaneDevelopingMap.domain,
        LocalUpperHalfPlaneProjectiveNormalization.domain,
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain] using
        B.affineMapSecondDeriv_hasDerivAt x hx

/-- The strengthened derivative-data atlas forgets to the metric-data atlas theorem. -/
noncomputable def hyperbolicLiouvilleProducesLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlasTheorem_of_derivativeData
    (h :
      HyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem) :
    HyperbolicLiouvilleProducesLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlasTheorem := by
  intro u hu
  rcases h u hu with ⟨A⟩
  exact ⟨A.toMetricDataAtlas⟩

/-- Public closed form of the strengthened derivative-data normalization-atlas theorem. -/
noncomputable def hyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem :
    HyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra
    hyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem_proved

/-- Public closed form of the strengthened metric-data normalization-atlas theorem. -/
noncomputable def hyperbolicLiouvilleProducesLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlasTheorem :
    HyperbolicLiouvilleProducesLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlasTheorem_of_derivativeData
    hyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem

/--
The strengthened metric-data normalization atlas, branch regularity, and the
coefficient-aware one-jet uniqueness theorem give real upper-half-plane branch
atlases.  Empty off-diagonal overlaps are vacuous and diagonal transitions are
identity transitions.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricData_branchContinuity_affineDerivative_oneJetUniqueness
    (hMetricData :
      HyperbolicLiouvilleProducesLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlasTheorem)
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem := by
  intro u hu
  rcases hMetricData u hu with ⟨A⟩
  let Aold : LocalMetricRecoveringSchwarzianNormalizationAtlas u :=
    A.toLocalMetricRecoveringSchwarzianNormalizationAtlas
  let R : LocalRealSchwarzianNormalizationAtlas u :=
    { toLocalMetricRecoveringSchwarzianNormalizationAtlas := Aold
      transition_realMobius := by
        intro z w
        by_cases hzw : z = w
        · subst w
          change (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch z)
          exact LocalUpperHalfPlaneDevelopingMap.hasRealMobiusTransition_self
            (A.normalizedBranch z)
        · by_cases hne :
            Set.Nonempty ((A.normalizedBranch z).domain ∩ (A.normalizedBranch w).domain)
          · change (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch w)
            exact
              A.hasOverlappingOffDiagonalRealTransitions_of_branchContinuity_affineDerivative_oneJetUniqueness
                hBranch hAffine hUnique hu z w hzw hne
          · refine ⟨1, ?_⟩
            intro x hxz hxw
            exfalso
            exact hne ⟨x, ⟨by simpa [Aold,
              LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.normalizedBranch,
              LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.toLocalMetricRecoveringSchwarzianNormalizationAtlas,
              LocalMetricRecoveringSchwarzianNormalizationAtlas.normalizedBranch] using hxz,
              by simpa [Aold,
                LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.normalizedBranch,
                LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.toLocalMetricRecoveringSchwarzianNormalizationAtlas,
                LocalMetricRecoveringSchwarzianNormalizationAtlas.normalizedBranch] using hxw⟩⟩ }
  exact ⟨R.toLocalRealUpperHalfPlaneBranchAtlas⟩

/--
The strengthened metric-data atlas route with branch regularity and
coefficient-aware local uniqueness supplied by the symbolic projective
derivative fields.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricData_projectiveFirstSecondDerivative_scalarClosed
    (hMetricData :
      HyperbolicLiouvilleProducesLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlasTheorem)
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem := by
  intro u hu
  rcases hMetricData u hu with ⟨A⟩
  let Aold : LocalMetricRecoveringSchwarzianNormalizationAtlas u :=
    A.toLocalMetricRecoveringSchwarzianNormalizationAtlas
  let R : LocalRealSchwarzianNormalizationAtlas u :=
    { toLocalMetricRecoveringSchwarzianNormalizationAtlas := Aold
      transition_realMobius := by
        intro z w
        by_cases hzw : z = w
        · subst w
          change (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch z)
          exact LocalUpperHalfPlaneDevelopingMap.hasRealMobiusTransition_self
            (A.normalizedBranch z)
        · by_cases hne :
            Set.Nonempty ((A.normalizedBranch z).domain ∩ (A.normalizedBranch w).domain)
          · change (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch w)
            exact
              A.hasOverlappingOffDiagonalRealTransitions_of_projectiveFirstSecondDerivative_scalarClosed
                hProjFirst hProjSecond hu z w hzw hne
          · refine ⟨1, ?_⟩
            intro x hxz hxw
            exfalso
            exact hne ⟨x, ⟨by simpa [Aold,
              LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.normalizedBranch,
              LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.toLocalMetricRecoveringSchwarzianNormalizationAtlas,
              LocalMetricRecoveringSchwarzianNormalizationAtlas.normalizedBranch] using hxz,
              by simpa [Aold,
                LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.normalizedBranch,
                LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.toLocalMetricRecoveringSchwarzianNormalizationAtlas,
                LocalMetricRecoveringSchwarzianNormalizationAtlas.normalizedBranch] using hxw⟩⟩ }
  exact ⟨R.toLocalRealUpperHalfPlaneBranchAtlas⟩

/--
The derivative-data atlas route to real Schwarzian normalization atlases:
coefficient agreement, branch derivative regularity, closedness of the one-jet
equality locus, and connected-overlap propagation are all supplied by the
atlas.  The remaining input is the pair-shaped local Schwarzian uniqueness
theorem.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_derivativeData_pairProjectiveDerivativeUniqueness
    (hDerivativeData :
      HyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem)
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem) :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem := by
  intro u hu
  rcases hDerivativeData u hu with ⟨A⟩
  let Aold : LocalMetricRecoveringSchwarzianNormalizationAtlas u :=
    A.toMetricDataAtlas.toLocalMetricRecoveringSchwarzianNormalizationAtlas
  let R : LocalRealSchwarzianNormalizationAtlas u :=
    { toLocalMetricRecoveringSchwarzianNormalizationAtlas := Aold
      transition_realMobius := by
        intro z w
        change (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch w)
        exact A.transition_realMobius_of_pairProjectiveDerivativeUniqueness
          hUnique hu z w }
  exact ⟨R⟩

/--
The derivative-data real-normalization route, after forgetting the
Schwarzian-normalization provenance, gives the real upper-half-plane branch
atlas theorem.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_derivativeData_pairProjectiveDerivativeUniqueness
    (hDerivativeData :
      HyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem)
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_realSchwarzian
    (hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_derivativeData_pairProjectiveDerivativeUniqueness
      hDerivativeData hUnique)

/--
Closed derivative-data atlas route using the proved Frobenius
metric-Schwarzian derivative-data construction.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianDerivativeData_pairProjectiveDerivativeUniqueness
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_derivativeData_pairProjectiveDerivativeUniqueness
    hyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem
    hUnique

/--
Closed derivative-data real Schwarzian-normalization route using the proved
Frobenius metric-Schwarzian derivative-data construction.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricSchwarzianDerivativeData_pairProjectiveDerivativeUniqueness
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem) :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_derivativeData_pairProjectiveDerivativeUniqueness
    hyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem
    hUnique

/--
Closed derivative-data real branch-atlas route.

The fixed-pair projective-derivative Schwarzian identity principle is now
proved, so the strengthened Frobenius derivative-data atlas directly produces
the real upper-half-plane branch atlas.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianDerivativeData_pairProjectiveDerivativeClosed :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianDerivativeData_pairProjectiveDerivativeUniqueness
    pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem_proved

/--
Closed derivative-data real Schwarzian-normalization route.

The fixed-pair projective-derivative Schwarzian identity principle is now
proved, so the strengthened Frobenius derivative-data atlas directly produces
the real Schwarzian-normalized atlas, before any branch-atlas erasure.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricSchwarzianDerivativeData_pairProjectiveDerivativeClosed :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricSchwarzianDerivativeData_pairProjectiveDerivativeUniqueness
    pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem_proved

/--
Public closed form of the local real Schwarzian-normalization theorem.

This keeps the Schwarzian ODE provenance and the real-transition proof in the
public chain; the branch-atlas theorem is then just its forgetful consequence.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricSchwarzianDerivativeData_pairProjectiveDerivativeClosed

/--
Public closed form of the local real upper-half-plane branch-atlas theorem.

The concrete metric-Schwarzian derivative-data atlas keeps the coefficient
agreement and projective derivative regularity needed for the real-transition
argument, so no broad arbitrary-branch transition hypothesis is required.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_realSchwarzian
    hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem

/--
%%handwave
name:
  Solve the local Schwarzian problem
statement:
  Let $u : U \to \mathbb R$ satisfy $\Delta u=e^{2u}$. Around every point of
  $U$ there is a holomorphic map $F : V \to \mathbb H$ such that
  $e^{2u}=|F'|^2/(\operatorname{Im}F)^2$ on $V$. The branches can be chosen so
  that any two which meet differ on their connected overlap by an element of
  $\mathrm{PSL}_2(\mathbb R)$.
proof:
  [The metric-Schwarzian construction supplies upper-half-plane branches which recover the metric and differ by real Möbius transformations on connected overlaps](lean:JJMath.hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem). This is exactly the asserted local solution.
-/
theorem solveLocalSchwarzianProblem :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem

/--
Closed real branch-atlas wrapper using the proved strengthened metric-data
normalization atlas.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_oneJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricData_branchContinuity_affineDerivative_oneJetUniqueness
    hyperbolicLiouvilleProducesLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlasTheorem
    hBranch hAffine hUnique

/--
The same strengthened metric-data atlas route, with the coefficient-aware
one-jet uniqueness theorem obtained from the two natural analytic inputs:
metric recovery supplies the missing second jet, and Schwarzian ODE uniqueness
uses the resulting two-jet.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_metricSecondJet_twoJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hSecond :
      PointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricSchwarzianData_branchContinuity_affineDerivative_oneJetUniqueness
    hBranch hAffine
    (pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem_of_metricSecondJet_twoJetUniqueness
      hSecond hTwoJet)

end

end JJMath
