import JJMath.Hyperbolic.Schwarzian.Developing

/-!
# Split Schwarzian theorem wrappers and hyperbolic specialization
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

/--
Sharper target: constant curvature produces Schwarzian data together with the
proof that the stored coefficient is the metric Schwarzian of `u`.

%%handwave
name:
  Constant curvature produces metric Schwarzian data
statement:
  This proposition asserts that every conformal factor satisfying $\Delta u=-Ke^{2u}$ determines holomorphic local Schwarzian data whose coefficient is $2(u_{zz}-u_z^2)$.
-/
def ConstantCurvatureProducesMetricSchwarzianDataTheorem : Prop :=
  ∀ (u : LocalConformalFactor) (K : ℝ),
    u.SolvesConstantCurvatureEquation K → Nonempty (LocalMetricSchwarzianData u)

/--
Concrete Frechet/Wirtinger derivative package target.

This is now the main low-level analytic boundary for producing the
half-Schwarzian coefficient from a constant-curvature conformal factor.  The
functions in the package are no longer arbitrary symbolic fields: they are the
canonical Frechet-level Wirtinger expressions built from `u.logDensity`.

%%handwave
name:
  Constant curvature produces canonical Wirtinger data
statement:
  This proposition asserts that every conformal factor satisfying $\Delta u=-Ke^{2u}$ has canonical Fréchet--Wirtinger fields satisfying the mixed-derivative, exponential-derivative, and Schwarzian product-rule identities.
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
Hyperbolic specialization of the metric-Schwarzian target: the local
Schwarzian coefficient is not merely holomorphic, but is identified with the
canonical metric Schwarzian of the Liouville factor.

%%handwave
name:
  Hyperbolic Liouville equation produces metric Schwarzian data
statement:
  This proposition asserts that every $u$ satisfying $\Delta u=e^{2u}$ determines holomorphic local Schwarzian data with coefficient $2(u_{zz}-u_z^2)$.
-/
def HyperbolicLiouvilleProducesMetricSchwarzianDataTheorem : Prop :=
  ∀ (u : LocalConformalFactor),
    u.SolvesLiouvilleEquation → Nonempty (LocalMetricSchwarzianData u)

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

%%handwave
name:
  Metric-Schwarzian Frobenius normalizations with derivative algebra
statement:
  This proposition asserts that at every point of a hyperbolic Liouville factor, its metric Schwarzian admits a centered normalized Frobenius quotient into $\mathbb H$ whose canonical pullback carries the full affine and Wirtinger derivative algebra.
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
Strengthened local output retaining both the metric-Schwarzian data and the
projective derivative algebra for the selected normalized branches.

%%handwave
name:
  Derivative-data Schwarzian normalization atlas from Liouville
statement:
  This proposition asserts that every hyperbolic Liouville factor has an atlas of normalized upper-half-plane branches which recover the metric Schwarzian and retain their first three projective derivative identities.
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

%%handwave
name:
  Assemble the derivative-data normalization atlas
statement:
  Assuming pointwise metric-Schwarzian Frobenius normalizations with derivative algebra, choose one at every point to form a normalization atlas retaining the metric identification and first three branch derivatives.
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

/-- Public closed form of the strengthened derivative-data normalization-atlas theorem.
%%handwave
name:
  Canonical derivative-data normalization atlas for a Liouville factor
statement:
  Every solution of $\Delta u=e^{2u}$ admits an atlas of metric-recovering normalized Frobenius branches with their Schwarzian and projective derivative data.
-/
noncomputable def hyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem :
    HyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlasTheorem_of_metricSchwarzian_frobeniusDerivativeAlgebra
    hyperbolicLiouvilleProducesMetricSchwarzianFrobeniusTwoJetNormalizationsDerivativeAlgebraTheorem_proved

/--
The derivative-data atlas route to real Schwarzian normalization atlases:
coefficient agreement, branch derivative regularity, closedness of the one-jet
equality locus, and connected-overlap propagation are all supplied by the
atlas.  The remaining input is the pair-shaped local Schwarzian uniqueness
theorem.

%%handwave
name:
  Real Schwarzian atlas from derivative data and one-jet uniqueness
statement:
  If a metric-recovering normalization atlas retains coefficient and derivative data, and equal-Schwarzian normalized branches with matching one-jets differ locally by real Möbius transformations, then the atlas has real Möbius transitions.
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

%%handwave
name:
  Real Schwarzian atlas from metric derivative data
statement:
  The canonical metric-Schwarzian derivative-data atlas together with pairwise projective-derivative uniqueness produces a local Schwarzian normalization atlas whose transitions lie in $\mathrm{PSL}_2(\mathbb R)$.
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

%%handwave
name:
  Closed derivative-data construction of the real Schwarzian atlas
statement:
  The proved equal-Schwarzian one-jet uniqueness principle applied to the canonical derivative-data Frobenius atlas yields real Möbius transitions between all normalized branches.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricSchwarzianDerivativeData_pairProjectiveDerivativeClosed :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricSchwarzianDerivativeData_pairProjectiveDerivativeUniqueness
    pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem_proved

/--
Public closed form of the local real Schwarzian-normalization theorem.

This keeps the Schwarzian ODE provenance and the real-transition proof in the
public chain; the branch-atlas theorem is then just its forgetful consequence.

%%handwave
name:
  Local real Schwarzian normalization theorem
statement:
  Every solution of $\Delta u=e^{2u}$ admits a metric-recovering atlas of Schwarzian-normalized upper-half-plane branches whose overlap transitions are real Möbius transformations.
-/
noncomputable def hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricSchwarzianDerivativeData_pairProjectiveDerivativeClosed

/--
Public closed form of the local real upper-half-plane branch-atlas theorem.

The concrete metric-Schwarzian derivative-data atlas keeps the coefficient
agreement and projective derivative regularity needed for the real-transition
argument, so no broad arbitrary-branch transition hypothesis is required.

%%handwave
name:
  Local real upper-half-plane branch atlas theorem
statement:
  Every hyperbolic Liouville factor admits local holomorphic maps to $\mathbb H$ recovering $e^{2u}|dz|^2$, and branches that overlap differ locally by elements of $\mathrm{PSL}_2(\mathbb R)$.
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

end

end JJMath
