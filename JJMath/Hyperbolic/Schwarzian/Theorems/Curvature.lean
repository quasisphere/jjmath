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
%%handwave
name:
  Wirtinger derivatives of a constant-curvature conformal factor
statement:
  Let \(u\) be a smooth conformal factor on \(\Omega\subset\mathbb C\) with
  \(\Delta u=-K e^{2u}\). Then the canonical first and second Wirtinger
  derivatives of \(u\), together with their product-rule identities, exist on
  \(\Omega\).
proof:
  Use the canonical Fréchet derivatives of the smooth function \(u\). The
  constant-curvature equation supplies the mixed-derivative identity, and the
  ordinary product rule supplies the derivatives of the quadratic terms.
-/
theorem constantCurvatureProducesWirtingerDerivativePackageTheorem :
    ConstantCurvatureProducesWirtingerDerivativePackageTheorem := by
  intro u K hK
  exact ⟨u.wirtingerDerivativePackage K hK⟩

/--
%%handwave
name:
  Constant curvature produces the metric Schwarzian
statement:
  Suppose the canonical Wirtinger derivatives are available for every smooth
  \(u\) satisfying \(\Delta u=-K e^{2u}\). Then
  \[S_u=2\bigl(u_{zz}-u_z^2\bigr)\]
  is holomorphic on the coordinate domain and is identified with the
  Schwarzian coefficient determined by \(u\).
proof:
  The Wirtinger product-rule calculation shows
  \(\partial_{\bar z}(u_{zz}-u_z^2)=0\). The Cauchy--Riemann criterion makes
  this expression holomorphic, and multiplication by two gives \(S_u\).
-/
theorem constantCurvatureProducesMetricSchwarzianDataTheorem_of_wirtingerDerivativePackage
    (hW : ConstantCurvatureProducesWirtingerDerivativePackageTheorem) :
    ConstantCurvatureProducesMetricSchwarzianDataTheorem := by
  intro u K hK
  rcases hW u K hK with ⟨W⟩
  exact ⟨W.toLocalMetricSchwarzianData hK⟩

/--
%%handwave
name:
  Holomorphicity of the metric Schwarzian at constant curvature
statement:
  If \(u\) satisfies \(\Delta u=-K e^{2u}\) on its coordinate domain, then
  \(S_u=2(u_{zz}-u_z^2)\) is holomorphic there and is the metric Schwarzian of
  \(u\).
proof:
  Construct the canonical Wirtinger derivatives of \(u\), then apply the
  product-rule cancellation of the mixed derivative of
  \(u_{zz}-u_z^2\).
-/
theorem constantCurvatureProducesMetricSchwarzianDataTheorem :
    ConstantCurvatureProducesMetricSchwarzianDataTheorem :=
  constantCurvatureProducesMetricSchwarzianDataTheorem_of_wirtingerDerivativePackage
    constantCurvatureProducesWirtingerDerivativePackageTheorem

/--
%%handwave
name:
  A metric Schwarzian is a holomorphic Schwarzian coefficient
statement:
  If every constant-curvature conformal factor has a holomorphic metric
  Schwarzian \(S_u=2(u_{zz}-u_z^2)\), then every such factor has a holomorphic
  Schwarzian coefficient on the same coordinate domain.
proof:
  Retain the holomorphic coefficient and forget only its additional
  identification with the derivatives of \(u\).
-/
theorem constantCurvatureProducesHolomorphicSchwarzianTheorem_of_metricSchwarzianData
    (h : ConstantCurvatureProducesMetricSchwarzianDataTheorem) :
    ConstantCurvatureProducesHolomorphicSchwarzianTheorem := by
  intro u K hK
  rcases h u K hK with ⟨M⟩
  exact ⟨M.toLocalSchwarzianData⟩

/--
%%handwave
name:
  Constant curvature yields a holomorphic Schwarzian coefficient
statement:
  For every smooth conformal factor \(u\) satisfying
  \(\Delta u=-K e^{2u}\), there is a holomorphic Schwarzian coefficient on the
  coordinate domain of \(u\).
proof:
  The constant-curvature calculation makes
  \(S_u=2(u_{zz}-u_z^2)\) holomorphic; use this metric Schwarzian as the
  required coefficient.
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
The holomorphic-Schwarzian theorem plus Frobenius-pair existence gives local
projective developing maps.
-/
def constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius
    (hS : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (hFrob : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    ConstantCurvatureProducesLocalProjectiveDevelopingMapsTheorem :=
  constantCurvatureProducesLocalProjectiveDevelopingMapsTheorem_of_schwarzian hS
    (holomorphicSchwarzianLocalProjectiveDevelopingMapTheorem_of_frobeniusPairExistence hFrob)

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

/--
%%handwave
name:
  Scaling the hyperbolic half-Schwarzian
statement:
  If \(q=u_{zz}-u_z^2\) is holomorphic for every solution of
  \(\Delta u=e^{2u}\), then \(S_u=2q\) is a holomorphic Schwarzian coefficient
  for every such solution.
proof:
  Multiply the holomorphic half-Schwarzian by two and retain the same domain.
-/
theorem hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem_of_halfSchwarzian
    (h : HyperbolicLiouvilleProducesHalfSchwarzianDataTheorem) :
    HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem := by
  intro u hu
  rcases h u hu with ⟨H⟩
  exact ⟨H.toLocalSchwarzianData⟩

/--
%%handwave
name:
  The hyperbolic half-Schwarzian from Wirtinger calculus
statement:
  Suppose the canonical Wirtinger derivatives are available for solutions of
  \(\Delta u=e^{2u}\). Then \(q=u_{zz}-u_z^2\) is holomorphic on the
  coordinate domain of every solution \(u\).
proof:
  Regard the Liouville equation as the constant-curvature equation with
  \(K=-1\). The mixed-derivative product-rule identity then gives
  \(\partial_{\bar z}q=0\).
-/
theorem hyperbolicLiouvilleProducesHalfSchwarzianDataTheorem_of_wirtingerDerivativePackage
    (hW : HyperbolicLiouvilleProducesWirtingerDerivativePackageTheorem) :
    HyperbolicLiouvilleProducesHalfSchwarzianDataTheorem := by
  intro u hu
  rcases hW u hu with ⟨W⟩
  exact ⟨W.toLocalHalfSchwarzianData
    ((u.solvesLiouvilleEquation_iff_solvesConstantCurvatureEquation_neg_one).mp hu)⟩

/--
%%handwave
name:
  The hyperbolic Schwarzian from Wirtinger calculus
statement:
  If canonical Wirtinger calculus is available for every solution of
  \(\Delta u=e^{2u}\), then \(S_u=2(u_{zz}-u_z^2)\) is holomorphic on the
  coordinate domain of \(u\).
proof:
  First obtain the holomorphic half-Schwarzian
  \(u_{zz}-u_z^2\), and then multiply it by two.
-/
theorem hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem_of_wirtingerDerivativePackage
    (hW : HyperbolicLiouvilleProducesWirtingerDerivativePackageTheorem) :
    HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem :=
  hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem_of_halfSchwarzian
    (hyperbolicLiouvilleProducesHalfSchwarzianDataTheorem_of_wirtingerDerivativePackage hW)

/--
%%handwave
name:
  Holomorphic Schwarzian of a hyperbolic conformal factor
statement:
  If \(u\) satisfies the hyperbolic Liouville equation
  \(\Delta u=e^{2u}\), then \(S_u=2(u_{zz}-u_z^2)\) is holomorphic on the
  coordinate domain of \(u\).
proof:
  This is the constant-curvature Schwarzian calculation specialized to
  \(K=-1\).
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
Hyperbolic Liouville data produces genuine local `ℍ`-valued developing maps
with the Poincare pullback squared-density formula.
-/
def HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem : Prop :=
  ∀ (u : LocalConformalFactor) ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ u.coordinateDomain →
      ∃ (S : LocalSchwarzianData u) (H : LocalUpperHalfPlaneDevelopingMap S),
        z ∈ H.domain

/--
%%handwave
name:
  Hyperbolic two-jet normalization of Frobenius coordinates
statement:
  Assume that hyperbolic conformal factors have holomorphic Schwarzians, the
  corresponding second-order equation has centered Frobenius bases, Möbius
  transformations act transitively on nondegenerate two-jets, and the
  normalized jet lands in \(\mathbb H\). Then every point of the coordinate
  domain has a centered Frobenius projective coordinate with a local
  \(\mathbb H\)-valued two-jet normalization.
proof:
  Choose the holomorphic Schwarzian and a centered Frobenius pair at the given
  point. Its ratio has a nondegenerate finite two-jet. Normalize that jet by a
  Möbius transformation and use the landing hypothesis to obtain the desired
  upper-half-plane branch.
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
%%handwave
name:
  Frobenius two-jet normalization from Schwarzian invariance
statement:
  Assume centered Frobenius solutions exist, postcomposition by Möbius maps
  preserves their Schwarzian, and the normalized jet lands in \(\mathbb H\).
  Then every hyperbolic Liouville solution has a locally normalized
  upper-half-plane Frobenius coordinate at each point.
proof:
  Schwarzian invariance gives Möbius transitivity for the Frobenius ratio.
  Apply the resulting two-jet normalization and then the upper-half-plane
  landing assertion.
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
%%handwave
name:
  Frobenius normalization from an upper-half-plane normal-form lift
statement:
  Suppose hyperbolic conformal factors have holomorphic Schwarzians, centered
  Frobenius bases exist, and the normal-form postcomposition of each Frobenius
  ratio lifts locally to \(\mathbb H\). Then every point admits a normalized
  upper-half-plane Frobenius coordinate.
proof:
  Choose the Schwarzian, the centered Frobenius ratio, and its base two-jet.
  Apply the assumed normal-form lift to this jet; its domain contains the base
  point and provides the required normalized branch.
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
%%handwave
name:
  Frobenius normalization from a prescribed two-jet normal form
statement:
  Suppose centered Frobenius coordinates exist for the holomorphic Schwarzian
  of every hyperbolic conformal factor, and every such coordinate admits an
  upper-half-plane normalization with a prescribed base two-jet. Then every
  point admits a normalized upper-half-plane Frobenius coordinate.
proof:
  At the chosen point, select the Schwarzian and a centered Frobenius ratio.
  Its base jet is defined and nondegenerate, so the normalization hypothesis
  gives the desired local branch containing that point.
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
%%handwave
name:
  Frobenius normalization from derivative identification
statement:
  Suppose the derivatives of every normal-form postcomposition of a centered
  Frobenius ratio are identified with its formal first three derivatives. Then,
  together with holomorphic Schwarzian and Frobenius existence, every point of
  a hyperbolic Liouville solution admits a normalized \(\mathbb H\)-valued
  Frobenius coordinate.
proof:
  The derivative identities produce the local upper-half-plane normal-form
  lift. Apply the preceding normalization construction to that lift.
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
%%handwave
name:
  Frobenius normalization from the canonical third derivative
statement:
  Suppose the canonical normal-form postcomposition of every centered
  Frobenius ratio has the prescribed third derivative at its base point. Then,
  assuming holomorphic Schwarzian and Frobenius existence, every point of a
  hyperbolic Liouville solution admits a normalized upper-half-plane
  Frobenius coordinate.
proof:
  The third-derivative identity yields the full normal-form normalization.
  Apply that normalization to the Frobenius ratio chosen at the point.
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
%%handwave
name:
  Frobenius normalization from derivatives of the solution ratio
statement:
  Suppose the affine ratio of every centered Frobenius pair has its stated
  complex derivative. Then holomorphic Schwarzian and Frobenius existence imply
  that every point of a hyperbolic Liouville solution admits a normalized
  upper-half-plane Frobenius coordinate.
proof:
  The derivative of the ratio and the chain rule identify the derivatives of
  its Möbius normal form. This gives the normal-form lift, to which the
  Frobenius normalization construction applies.
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
%%handwave
name:
  Derivative algebra of a normalized Frobenius coordinate
statement:
  Let \(u\) solve \(\Delta u=e^{2u}\), let \(S\) be a holomorphic Schwarzian
  coefficient for \(u\), and let \(z\) lie in its coordinate domain. If the
  Schwarzian equation admits centered Frobenius bases, then there is a
  Frobenius ratio normalized into \(\mathbb H\) near \(z\) whose canonical
  pullback conformal factor has the required first three affine derivatives
  and Wirtinger derivative identities.
proof:
  Choose a centered Frobenius pair and put its ratio into the canonical Möbius
  normal form. The explicit first three derivative formulas give the
  derivative identifications. Smoothness of the ratio and its derivative gives
  the pullback regularity, and these two ingredients yield the canonical
  derivative algebra on a ball about \(z\).
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
%%handwave
name:
  Metric Schwarzian normalization with derivative algebra
statement:
  Suppose every hyperbolic Liouville solution has its metric Schwarzian and
  every holomorphic Schwarzian equation admits centered Frobenius bases. Then,
  at each point, there is a centered Frobenius ratio normalized into
  \(\mathbb H\); its coefficient is the metric Schwarzian of \(u\), and its
  canonical pullback carries the full affine and Wirtinger derivative algebra.
proof:
  Choose the metric Schwarzian of \(u\), apply the fixed-coefficient Frobenius
  construction to its underlying holomorphic coefficient, and retain the
  metric identification together with the resulting normalization and
  derivative identities.
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
%%handwave
name:
  Canonical Frobenius normalization of a hyperbolic metric
statement:
  Every solution of \(\Delta u=e^{2u}\) and every point in its coordinate
  domain admit a centered Frobenius ratio normalized into \(\mathbb H\), with
  coefficient \(2(u_{zz}-u_z^2)\) and with the canonical pullback derivative
  algebra on a neighborhood of the point.
proof:
  Use holomorphicity of the metric Schwarzian and local analytic existence for
  the Frobenius equation, then apply the metric-Schwarzian normalization with
  derivative algebra.
-/
theorem hyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem_proved :
    HyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem :=
  hyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem
    hyperbolicLiouvilleProducesMetricSchwarzianDataTheorem
    holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic

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
