import JJMath.Hyperbolic.Converse.LocalInverseTransition
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.Sort
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Split analytic continuation targets for the partial converse
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]


def AnalyticContinuationFromLocalSolvingTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localCurvatureConstructions :
      g.HasCurvatureLiouvilleDevelopingConstructionAtlas),
    Nonempty
      (ContinuationFromCurvatureLocalConstructions
        x₀ g localCurvatureConstructions)

/-- The local model atlas associated to curvature-derived local constructions. -/
def localModelsFromCurvatureConstructions
    (g : HyperbolicMetric X)
    (localCurvatureConstructions :
      g.HasCurvatureLiouvilleDevelopingConstructionAtlas) :
    HyperbolicLocalModelAtlas X g :=
  (LocalLiouvilleDevelopingConstructionAtlas.toLocalLiouvilleDevelopingSolutionAtlas
    localCurvatureConstructions.developingConstructionAtlas).toHyperbolicLocalModelAtlas

/--
Global theorem target for analytically continuing any chosen local
upper-half-plane model atlas.
-/
structure ContinuationFromLocalModels
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- The local-model continuation pipeline. -/
  continuationPipeline : HyperbolicLocalModelContinuationPipeline X x₀ g
  /-- The pipeline uses the selected local models. -/
  continuation_uses_localModels :
    continuationPipeline.localModels = localModels

namespace ContinuationFromLocalModels

/-- Forget the fixed-atlas wrapper and keep the continuation pipeline. -/
def toHyperbolicLocalModelContinuationPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (C : ContinuationFromLocalModels x₀ g localModels) :
    HyperbolicLocalModelContinuationPipeline X x₀ g :=
  C.continuationPipeline

/-- Forget the fixed-atlas wrapper and keep the developing-continuation data. -/
def toHyperbolicDevelopingContinuationData
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (C : ContinuationFromLocalModels x₀ g localModels) :
    HyperbolicDevelopingContinuationData X x₀ g :=
  C.continuationPipeline.toHyperbolicDevelopingContinuationData

/-- The lifted developing map obtained from the fixed-atlas continuation package. -/
def toLiftedHyperbolicDevelopingMap
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (C : ContinuationFromLocalModels x₀ g localModels) :
    LiftedHyperbolicDevelopingMap X x₀ g :=
  C.continuationPipeline.toLiftedHyperbolicDevelopingMap

/-- The ordinary developing map obtained from the fixed-atlas continuation package. -/
def toHyperbolicDevelopingMap
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (C : ContinuationFromLocalModels x₀ g localModels) :
    HyperbolicDevelopingMap X x₀ g :=
  C.continuationPipeline.toHyperbolicDevelopingMap

end ContinuationFromLocalModels

/--
Local agreement boundary for a continued developing map and a local-model
atlas whose transition data is only local on overlaps.
-/
def HyperbolicDevelopingAgreesWithLocalTransitionModels
    {x₀ : X} {g : HyperbolicMetric X}
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    (cover : SimplyConnectedCover X x₀) (dev : cover.total → ℍ) : Prop :=
  ∀ y, ∃ U : Set cover.total,
    IsOpen U ∧ y ∈ U ∧
      ∃ (x : X) (A : RealMobiusRepresentative),
        (∀ y', y' ∈ U → cover.projection y' ∈ (localModels.chartAt x).domain) ∧
          ∀ y', y' ∈ U →
            dev y' =
              realMobiusRepresentativeAction A
                ((localModels.chartAt x).toUpperHalfPlane (cover.projection y'))

namespace HyperbolicDevelopingAgreesWithLocalTransitionModels

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {cover : SimplyConnectedCover X x₀} {dev : cover.total → ℍ}

omit [RiemannSurface X] in
/-- Local agreement with local-transition models forces pointwise continuity.

%%handwave
name: Local model agreement makes the developing map continuous at every point
statement: Let $dev$ on a simply connected cover agree near each lift $y$ with a real Möbius transformation composed with a local hyperbolic chart of the projected point. Then $dev$ is continuous at $y$.
proof: The cover projection, local chart, and real Möbius action are continuous. Their composite is continuous at $y$, and the assumed neighborhood equality transfers continuity to $dev$.
-/
theorem continuousAt
    (h : HyperbolicDevelopingAgreesWithLocalTransitionModels localModels cover dev)
    (y : cover.total) :
    ContinuousAt dev y := by
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let localModelFun : cover.total → ℍ := fun y' =>
    realMobiusRepresentativeAction A
      ((localModels.chartAt x).toUpperHalfPlane (cover.projection y'))
  have hy_domain : cover.projection y ∈ (localModels.chartAt x).domain :=
    hdomain y hyU
  have hpost :
      ContinuousAt
        (fun x' : X =>
          realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane x'))
        (cover.projection y) :=
    (localModels.chartAt x).realMobius_postcomp_continuousAt A hy_domain
  have hlocal : ContinuousAt localModelFun y := by
    exact hpost.comp (cover.projection_continuousAt y)
  have heq : dev =ᶠ[nhds y] localModelFun := by
    filter_upwards [hUopen.mem_nhds hyU] with y' hy'
    exact hagree y' hy'
  exact hlocal.congr_of_eventuallyEq heq

omit [RiemannSurface X] in
/-- Local agreement with local-transition models forces continuity.

%%handwave
name: Local model agreement makes the developing map continuous
statement: If a developing map agrees locally everywhere with Möbius-transformed hyperbolic model charts, then it is continuous on the entire cover.
proof: Apply the pointwise continuity result at every point.
-/
theorem continuous
    (h : HyperbolicDevelopingAgreesWithLocalTransitionModels localModels cover dev) :
    Continuous dev := by
  rw [continuous_iff_continuousAt]
  intro y
  exact h.continuousAt y

/-- Global-transition local agreement forgets to local-transition local agreement.

%%handwave
name: Agreement with a global model atlas gives local-transition agreement
statement: If $dev$ agrees locally with charts of a global hyperbolic local-model atlas, then it agrees locally with the same charts viewed in the associated local-transition atlas.
proof: The local charts and agreement formulas are unchanged by forgetting the global transition structure.
-/
theorem of_global
    {A : HyperbolicLocalModelAtlas X g}
    {cover : SimplyConnectedCover X x₀} {dev : cover.total → ℍ}
    (h : HyperbolicDevelopingAgreesWithLocalModels A cover dev) :
    HyperbolicDevelopingAgreesWithLocalTransitionModels
      A.toLocalTransitionAtlas cover dev := by
  intro y
  rcases h y with ⟨U, hUopen, hyU, x, M, hdomain, hagree⟩
  exact ⟨U, hUopen, hyU, x, M, hdomain, hagree⟩

end HyperbolicDevelopingAgreesWithLocalTransitionModels

/--
Continuation fields for a fixed local-transition local-model atlas.

This is the honest analytic-continuation endpoint for componentwise overlap
data: it has the same developing map, holonomy, equivariance, and metric
pullback fields as the old fixed-atlas target, but its local agreement field
refers only to local real-Mobius transition models.
-/
structure HyperbolicDevelopingLocalTransitionContinuationDataFields
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- The simply connected cover on which analytic continuation is single-valued. -/
  cover : SimplyConnectedCover X x₀
  /-- The analytically continued developing map. -/
  dev : cover.total → ℍ
  /-- The pullback of `g` to the cover. -/
  coverMetric : ConformalMetric cover.total
  /-- The cover metric is the pullback of the base metric along the projection. -/
  coverMetric_pullback :
    PullsBackMetric cover.projection g.toConformalMetric coverMetric
  /-- The developing map has holomorphic local-biholomorphic regularity on the cover. -/
  dev_regular : HyperbolicDevelopingMapRegularity cover dev
  /-- Lifted real holonomy obtained by monodromy of the local models. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Pullback identity: `dev^* g_ℍ = projection^* g`. -/
  pullback_metric :
    PullsBackMetric dev upperHalfPlaneConformalMetric coverMetric
  /-- Equivariance with respect to deck transformations and lifted holonomy. -/
  equivariant :
    ∀ γ y, dev (cover.deckAction γ y) = holonomyLift.upperHalfPlaneAction γ (dev y)
  /-- The developing map locally agrees with analytic continuation of the local models. -/
  agrees_with_local_models :
    HyperbolicDevelopingAgreesWithLocalTransitionModels localModels cover dev

namespace HyperbolicDevelopingLocalTransitionContinuationDataFields

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

omit [RiemannSurface X] in
/-- Local-transition continuation fields supply continuity of `dev`.

%%handwave
name: Local-transition continuation fields have a continuous developing map
statement: For any package of local-transition continuation fields, its developing map $dev$ is continuous.
proof: Apply continuity from local-model agreement to the agreement data stored in the package.
-/
theorem dev_continuous
    (F : HyperbolicDevelopingLocalTransitionContinuationDataFields
      x₀ g localModels) :
    Continuous F.dev :=
  F.dev_regular.continuous

omit [RiemannSurface X] in
/-- Local-transition continuation fields supply chartwise holomorphicity.

%%handwave
name: Local-transition continuation fields have a holomorphic developing map
statement: For every local-transition continuation field package and every cover point, the coordinate expression of $dev$ is complex differentiable at that point.
proof: This is the chartwise holomorphicity field carried by the continuation package.
-/
theorem dev_holomorphic
    (F : HyperbolicDevelopingLocalTransitionContinuationDataFields
      x₀ g localModels) :
    HyperbolicDevelopingMapHolomorphic F.cover F.dev :=
  F.dev_regular.holomorphic

/-- Forget local-model provenance and keep the lifted developing map. -/
def toLiftedHyperbolicDevelopingMap
    (F : HyperbolicDevelopingLocalTransitionContinuationDataFields
      x₀ g localModels) :
    LiftedHyperbolicDevelopingMap X x₀ g where
  cover := F.cover
  dev := F.dev
  coverMetric := F.coverMetric
  coverMetric_pullback := F.coverMetric_pullback
  dev_regular := F.dev_regular
  holonomyLift := F.holonomyLift
  pullback_metric := F.pullback_metric
  equivariant := F.equivariant

/-- Forget local-model provenance and keep the ordinary developing map. -/
def toHyperbolicDevelopingMap
    (F : HyperbolicDevelopingLocalTransitionContinuationDataFields
      x₀ g localModels) :
    HyperbolicDevelopingMap X x₀ g :=
  F.toLiftedHyperbolicDevelopingMap.toHyperbolicDevelopingMap

end HyperbolicDevelopingLocalTransitionContinuationDataFields

/--
Continuation from a fixed local-transition model atlas.
-/
structure ContinuationFromLocalTransitionModels
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- The explicit continuation fields. -/
  continuationFields :
    HyperbolicDevelopingLocalTransitionContinuationDataFields
      x₀ g localModels

namespace ContinuationFromLocalTransitionModels

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- Forget the fixed-atlas wrapper and keep the lifted developing map. -/
def toLiftedHyperbolicDevelopingMap
    (C : ContinuationFromLocalTransitionModels x₀ g localModels) :
    LiftedHyperbolicDevelopingMap X x₀ g :=
  C.continuationFields.toLiftedHyperbolicDevelopingMap

/-- Forget the fixed-atlas wrapper and keep the ordinary developing map. -/
def toHyperbolicDevelopingMap
    (C : ContinuationFromLocalTransitionModels x₀ g localModels) :
    HyperbolicDevelopingMap X x₀ g :=
  C.continuationFields.toHyperbolicDevelopingMap

/-- Old fixed-atlas continuation forgets to local-transition continuation. -/
def ofGlobalContinuation
    {A : HyperbolicLocalModelAtlas X g}
    (C : ContinuationFromLocalModels x₀ g A) :
    ContinuationFromLocalTransitionModels x₀ g A.toLocalTransitionAtlas :=
  let D := C.toHyperbolicDevelopingContinuationData
  { continuationFields :=
    { cover := D.cover
      dev := D.dev
      coverMetric := D.coverMetric
      coverMetric_pullback := D.coverMetric_pullback
      dev_regular := D.dev_regular
      holonomyLift := D.holonomyLift
      pullback_metric := D.pullback_metric
      equivariant := D.equivariant
      agrees_with_local_models :=
        by
          have hUses : D.localModels = A := by
            have hUsesData :
                D.localModels = C.continuationPipeline.localModels := by
              simpa [D, ContinuationFromLocalModels.toHyperbolicDevelopingContinuationData]
                using C.continuationPipeline.continuation_uses_localModels
            exact hUsesData.trans C.continuation_uses_localModels
          have hAgree : HyperbolicDevelopingAgreesWithLocalModels A D.cover D.dev := by
            simpa [hUses] using D.agrees_with_local_models
          exact
            HyperbolicDevelopingAgreesWithLocalTransitionModels.of_global
              hAgree } }

end ContinuationFromLocalTransitionModels

/--
Explicit fields for analytic continuation from a fixed local-model atlas.

This is the same data as `HyperbolicDevelopingContinuationData`, but with the
chosen local model atlas fixed as a parameter.  It lets the continuation
boundary be attacked field by field: construct the cover and continued map,
prove the pullback identity, construct monodromy, prove equivariance, and prove
agreement with the local charts.
-/
structure HyperbolicDevelopingContinuationDataFields
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- The simply connected cover on which analytic continuation is single-valued. -/
  cover : SimplyConnectedCover X x₀
  /-- The analytically continued developing map. -/
  dev : cover.total → ℍ
  /-- The pullback of `g` to the cover. -/
  coverMetric : ConformalMetric cover.total
  /-- The cover metric is the pullback of the base metric along the projection. -/
  coverMetric_pullback :
    PullsBackMetric cover.projection g.toConformalMetric coverMetric
  /-- The developing map has holomorphic local-biholomorphic regularity on the cover. -/
  dev_regular : HyperbolicDevelopingMapRegularity cover dev
  /-- Lifted real holonomy obtained by monodromy of the local models. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Pullback identity: `dev^* g_ℍ = projection^* g`. -/
  pullback_metric :
    PullsBackMetric dev upperHalfPlaneConformalMetric coverMetric
  /-- Equivariance with respect to deck transformations and lifted holonomy. -/
  equivariant :
    ∀ γ y, dev (cover.deckAction γ y) = holonomyLift.upperHalfPlaneAction γ (dev y)
  /-- The developing map locally agrees with analytic continuation of the local models. -/
  agrees_with_local_models :
    HyperbolicDevelopingAgreesWithLocalModels localModels cover dev

/-- The canonical first field of continuation data: the path-homotopy universal cover. -/
def canonicalContinuationCover (x₀ : X) : SimplyConnectedCover X x₀ :=
  PathHomotopyUniversalCover.simplyConnectedCoverOfRiemannSurface

/-- The canonical pulled-back metric on the path-homotopy continuation cover. -/
def canonicalContinuationCoverMetric (x₀ : X) (g : HyperbolicMetric X) :
    ConformalMetric (canonicalContinuationCover x₀).total :=
  PathHomotopyUniversalCover.pullbackConformalMetric (x₀ := x₀) g.toConformalMetric

/-- The canonical cover metric is the pullback of the base metric.

%%handwave
name: The canonical cover metric is the pullback of the base metric
statement: For the canonical path-homotopy cover $π:X̃→X$, the canonical cover metric satisfies $π^*g=g̃$.
proof: This is the defining pullback property of the canonical cover metric, expressed in compatible source and target charts.
-/
theorem canonicalContinuationCoverMetric_pullback
    (x₀ : X) (g : HyperbolicMetric X) :
    PullsBackMetric
      (canonicalContinuationCover x₀).projection
      g.toConformalMetric
      (canonicalContinuationCoverMetric x₀ g) :=
  PathHomotopyUniversalCover.pullsBackMetric_endpoint_pullbackConformalMetric
    (x₀ := x₀) g.toConformalMetric

/--
Local-transition continuation fields after fixing the canonical cover and its
canonical pulled-back metric.

This removes the bookkeeping choices of cover and cover metric from the
local-transition continuation boundary while leaving the analytic,
pullback-metric, holonomy, equivariance, and local-agreement obligations
unchanged.
-/
structure HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- The analytically continued developing map on the canonical cover. -/
  dev : (canonicalContinuationCover x₀).total → ℍ
  /-- The developing map has holomorphic local-biholomorphic regularity. -/
  dev_regular :
    HyperbolicDevelopingMapRegularity (canonicalContinuationCover x₀) dev
  /-- Lifted real holonomy obtained by monodromy of the local-transition models. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Pullback identity against the proved canonical pulled-back metric. -/
  pullback_metric :
    PullsBackMetric dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g)
  /-- Equivariance with respect to deck transformations and lifted holonomy. -/
  equivariant :
    ∀ γ y,
      dev ((canonicalContinuationCover x₀).deckAction γ y) =
        holonomyLift.upperHalfPlaneAction γ (dev y)
  /-- The developing map locally agrees with analytic continuation of the local-transition models. -/
  agrees_with_local_models :
    HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
      (canonicalContinuationCover x₀) dev

namespace HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Fields on the fixed canonical cover and metric fold back into the original
local-transition continuation-fields record.
-/
def toHyperbolicDevelopingLocalTransitionContinuationDataFields
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric
        x₀ g localModels) :
    HyperbolicDevelopingLocalTransitionContinuationDataFields
      x₀ g localModels where
  cover := canonicalContinuationCover x₀
  dev := F.dev
  coverMetric := canonicalContinuationCoverMetric x₀ g
  coverMetric_pullback := canonicalContinuationCoverMetric_pullback x₀ g
  dev_regular := F.dev_regular
  holonomyLift := F.holonomyLift
  pullback_metric := F.pullback_metric
  equivariant := F.equivariant
  agrees_with_local_models := F.agrees_with_local_models

/-- Forgetting the specified canonical cover metric preserves the developing map.

%%handwave
name: Forgetting the canonical metric preserves the developing map
statement: When canonical-cover-metric local-transition fields are viewed as ordinary local-transition continuation fields, their developing map is unchanged.
proof: The forgetful construction copies the developing-map field.
-/
@[simp]
theorem toHyperbolicDevelopingLocalTransitionContinuationDataFields_dev
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric
        x₀ g localModels) :
    F.toHyperbolicDevelopingLocalTransitionContinuationDataFields.dev = F.dev :=
  rfl

/-- Forgetting the specified canonical cover metric retains that metric as the underlying cover metric.

%%handwave
name: Forgetting the canonical metric retains it as the cover metric
statement: When canonical-cover-metric local-transition fields are viewed as ordinary fields, their cover metric is exactly the canonical pullback metric.
proof: The forgetful construction assigns the specified canonical metric to the underlying cover-metric field.
-/
@[simp]
theorem toHyperbolicDevelopingLocalTransitionContinuationDataFields_coverMetric
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric
        x₀ g localModels) :
    F.toHyperbolicDevelopingLocalTransitionContinuationDataFields.coverMetric =
      canonicalContinuationCoverMetric x₀ g :=
  rfl

end HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric

/--
Real Mobius representatives preserve the Poincare conformal metric in the
project's concrete chartwise pullback-metric sense.

%%handwave
name: Real Möbius transformations preserve the Poincaré metric
statement: For every real Möbius representative $A$, its action on $ℍ$ satisfies $A^*g_{ℍ}=g_{ℍ}$.
proof: In complex coordinates, use the derivative formula for the fractional-linear action and the formula for the imaginary part of $A·z$; the conformal factors cancel pointwise.
-/
theorem realMobiusRepresentativeAction_pullsBack_upperHalfPlaneConformalMetric
    (A : RealMobiusRepresentative) :
    PullsBackMetric
      (realMobiusRepresentativeAction A)
      upperHalfPlaneConformalMetric
      upperHalfPlaneConformalMetric where
  in_charts := by
    intro sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas p hp hAp
    let c : OpenPartialHomeomorph ℍ ℂ :=
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph
        UpperHalfPlane.coe UpperHalfPlane.isOpenEmbedding_coe
    have hsource_eq : sourceChart = c := by
      simpa [c] using sourceChart_mem_atlas
    have htarget_eq : targetChart = c := by
      simpa [c] using targetChart_mem_atlas
    subst sourceChart
    subst targetChart
    let localMap : ℂ → ℂ :=
      fun z : ℂ =>
        (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ)
    refine ⟨c.target, localMap, c.open_target, c.map_source hp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact hz
    · intro z hz
      exact c.map_target hz
    · intro z _hz
      simp
    · intro z hz
      have hz_im : 0 < z.im := by
        simpa [c] using hz
      simpa [localMap, c, UpperHalfPlane.ofComplex_apply_of_im_pos hz_im] using
        (mem_chart_target ℂ
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) z)))
    · intro z hz
      have hz_im : 0 < z.im := by
        simpa [c] using hz
      have hsymm :
          (c.symm z : ℍ) = ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) := by
        ext
        simpa [c, UpperHalfPlane.ofComplex_apply_of_im_pos hz_im] using
          (c.right_inv hz)
      rw [hsource_eq]
      simp [localMap, c, hsymm]
    · simpa [localMap, c] using
        realMobiusRepresentativeAction_differentiableAt A p
    · have hmetric := realMobiusRepresentativeAction_deriv_hyperbolicNormSq A p
      have hmetric' :
          ((p : ℂ).im ^ 2)⁻¹ =
            ((realMobiusRepresentativeAction A p : ℂ).im ^ 2)⁻¹ *
              Complex.normSq
                (deriv
                  (fun z : ℂ =>
                    (realMobiusRepresentativeAction A
                      ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
                  p) := by
        calc
          ((p : ℂ).im ^ 2)⁻¹ =
              Complex.normSq
                (deriv
                  (fun z : ℂ =>
                    (realMobiusRepresentativeAction A
                      ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
                  p) /
                ((realMobiusRepresentativeAction A p : ℂ).im ^ 2) := by
            simpa [one_div] using hmetric.symm
          _ =
              ((realMobiusRepresentativeAction A p : ℂ).im ^ 2)⁻¹ *
                Complex.normSq
                  (deriv
                    (fun z : ℂ =>
                      (realMobiusRepresentativeAction A
                        ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
                    p) := by
            rw [div_eq_mul_inv, mul_comm]
      simpa [upperHalfPlaneConformalMetric, poincareDensitySqInChart, localMap, c] using
        hmetric'

/--
The exact remaining continuation fields after fixing the cover.

This is only a field-by-field decomposition of
`HyperbolicDevelopingContinuationDataFields`; it does not weaken any analytic
condition.  In particular, `dev_regular`, `pullback_metric`, lifted holonomy,
equivariance, and local-model agreement are still the original target fields.
-/
structure HyperbolicDevelopingContinuationDataFieldsOnCover
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g)
    (cover : SimplyConnectedCover X x₀) where
  /-- The analytically continued developing map on the fixed cover. -/
  dev : cover.total → ℍ
  /-- The pullback of `g` to the fixed cover. -/
  coverMetric : ConformalMetric cover.total
  /-- The cover metric is the pullback of the base metric along the projection. -/
  coverMetric_pullback :
    PullsBackMetric cover.projection g.toConformalMetric coverMetric
  /-- The developing map has holomorphic local-biholomorphic regularity on the fixed cover. -/
  dev_regular : HyperbolicDevelopingMapRegularity cover dev
  /-- Lifted real holonomy obtained by monodromy of the local models. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Pullback identity: `dev^* g_ℍ = projection^* g`. -/
  pullback_metric :
    PullsBackMetric dev upperHalfPlaneConformalMetric coverMetric
  /-- Equivariance with respect to deck transformations and lifted holonomy. -/
  equivariant :
    ∀ γ y, dev (cover.deckAction γ y) = holonomyLift.upperHalfPlaneAction γ (dev y)
  /-- The developing map locally agrees with analytic continuation of the local models. -/
  agrees_with_local_models :
    HyperbolicDevelopingAgreesWithLocalModels localModels cover dev

namespace HyperbolicDevelopingContinuationDataFields

/-- Explicit continuation fields supply continuity of the continued developing map.

%%handwave
name: Explicit continuation fields have a continuous developing map
statement: For every continuation field package built from a global local-model atlas, the developing map $dev$ is continuous.
proof: The package supplies local agreement with the global models; forget to local-transition agreement and apply local continuity.
-/
theorem dev_continuous
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (F : HyperbolicDevelopingContinuationDataFields x₀ g localModels) :
    Continuous F.dev :=
  F.dev_regular.continuous

/-- Explicit continuation fields supply chartwise holomorphicity of the continued developing map.

%%handwave
name: Explicit continuation fields have a holomorphic developing map
statement: For every continuation field package from a global local-model atlas, $dev$ is holomorphic in surface charts.
proof: This is the chartwise holomorphicity field included in the package.
-/
theorem dev_holomorphic
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (F : HyperbolicDevelopingContinuationDataFields x₀ g localModels) :
    HyperbolicDevelopingMapHolomorphic F.cover F.dev :=
  F.dev_regular.holomorphic

/-- Fold explicit continuation fields into continuation data. -/
def toHyperbolicDevelopingContinuationData
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (F : HyperbolicDevelopingContinuationDataFields x₀ g localModels) :
    HyperbolicDevelopingContinuationData X x₀ g where
  localModels := localModels
  cover := F.cover
  dev := F.dev
  coverMetric := F.coverMetric
  coverMetric_pullback := F.coverMetric_pullback
  dev_regular := F.dev_regular
  holonomyLift := F.holonomyLift
  pullback_metric := F.pullback_metric
  equivariant := F.equivariant
  agrees_with_local_models := F.agrees_with_local_models

/-- Fold explicit continuation fields into the local-model continuation package. -/
def toContinuationFromLocalModels
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (F : HyperbolicDevelopingContinuationDataFields x₀ g localModels) :
    ContinuationFromLocalModels x₀ g localModels where
  continuationPipeline :=
    { localModels := localModels
      continuationData := F.toHyperbolicDevelopingContinuationData
      continuation_uses_localModels := rfl }
  continuation_uses_localModels := rfl

/-- Old fixed-atlas fields forget to local-transition fixed-atlas fields. -/
def toLocalTransitionFields
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (F : HyperbolicDevelopingContinuationDataFields x₀ g localModels) :
    HyperbolicDevelopingLocalTransitionContinuationDataFields
      x₀ g localModels.toLocalTransitionAtlas where
  cover := F.cover
  dev := F.dev
  coverMetric := F.coverMetric
  coverMetric_pullback := F.coverMetric_pullback
  dev_regular := F.dev_regular
  holonomyLift := F.holonomyLift
  pullback_metric := F.pullback_metric
  equivariant := F.equivariant
  agrees_with_local_models :=
    HyperbolicDevelopingAgreesWithLocalTransitionModels.of_global
      F.agrees_with_local_models

end HyperbolicDevelopingContinuationDataFields

namespace HyperbolicDevelopingContinuationDataFieldsOnCover

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    {cover : SimplyConnectedCover X x₀}

/-- Fixed-cover continuation fields fold back into the original continuation-fields record. -/
def toHyperbolicDevelopingContinuationDataFields
    (F : HyperbolicDevelopingContinuationDataFieldsOnCover x₀ g localModels cover) :
    HyperbolicDevelopingContinuationDataFields x₀ g localModels where
  cover := cover
  dev := F.dev
  coverMetric := F.coverMetric
  coverMetric_pullback := F.coverMetric_pullback
  dev_regular := F.dev_regular
  holonomyLift := F.holonomyLift
  pullback_metric := F.pullback_metric
  equivariant := F.equivariant
  agrees_with_local_models := F.agrees_with_local_models

/-- Forgetting the explicit cover retains the same simply connected covering.

%%handwave
name: Forgetting an explicitly fixed cover preserves that cover
statement: When continuation fields on a specified simply connected cover are viewed as existential-cover fields, the underlying cover is the same specified cover.
proof: This is immediate from the forgetful construction.
-/
@[simp]
theorem toHyperbolicDevelopingContinuationDataFields_cover
    (F : HyperbolicDevelopingContinuationDataFieldsOnCover x₀ g localModels cover) :
    F.toHyperbolicDevelopingContinuationDataFields.cover = cover :=
  rfl

/-- Forgetting the explicit cover retains the same developing map.

%%handwave
name: Forgetting an explicitly fixed cover preserves the developing map
statement: The developing map is unchanged when fields on a specified cover are viewed as general continuation fields.
proof: The forgetful construction copies $dev$.
-/
@[simp]
theorem toHyperbolicDevelopingContinuationDataFields_dev
    (F : HyperbolicDevelopingContinuationDataFieldsOnCover x₀ g localModels cover) :
    F.toHyperbolicDevelopingContinuationDataFields.dev = F.dev :=
  rfl

end HyperbolicDevelopingContinuationDataFieldsOnCover

/-- Exact remaining continuation fields on the canonical path-homotopy cover. -/
abbrev HyperbolicDevelopingContinuationDataFieldsOnCanonicalCover
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) :=
  HyperbolicDevelopingContinuationDataFieldsOnCover
    x₀ g localModels (canonicalContinuationCover x₀)

/--
Exact remaining continuation fields after fixing both the canonical cover and
its proved pulled-back metric.

This removes the already-constructed `cover`, `coverMetric`, and
`coverMetric_pullback` fields from the worklist while keeping all analytic,
metric, holonomy, equivariance, and local-model obligations unchanged.
-/
structure HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetric
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- The analytically continued developing map on the canonical cover. -/
  dev : (canonicalContinuationCover x₀).total → ℍ
  /-- The developing map has holomorphic local-biholomorphic regularity. -/
  dev_regular :
    HyperbolicDevelopingMapRegularity (canonicalContinuationCover x₀) dev
  /-- Lifted real holonomy obtained by monodromy of the local models. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Pullback identity against the proved canonical pulled-back metric. -/
  pullback_metric :
    PullsBackMetric dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g)
  /-- Equivariance with respect to deck transformations and lifted holonomy. -/
  equivariant :
    ∀ γ y,
      dev ((canonicalContinuationCover x₀).deckAction γ y) =
        holonomyLift.upperHalfPlaneAction γ (dev y)
  /-- The developing map locally agrees with analytic continuation of the local models. -/
  agrees_with_local_models :
    HyperbolicDevelopingAgreesWithLocalModels localModels
      (canonicalContinuationCover x₀) dev

namespace HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetric

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/--
Fields remaining after fixing the canonical cover metric fold back into the
original all-fields continuation record.
-/
def toHyperbolicDevelopingContinuationDataFields
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetric
        x₀ g localModels) :
    HyperbolicDevelopingContinuationDataFields x₀ g localModels where
  cover := canonicalContinuationCover x₀
  dev := F.dev
  coverMetric := canonicalContinuationCoverMetric x₀ g
  coverMetric_pullback := canonicalContinuationCoverMetric_pullback x₀ g
  dev_regular := F.dev_regular
  holonomyLift := F.holonomyLift
  pullback_metric := F.pullback_metric
  equivariant := F.equivariant
  agrees_with_local_models := F.agrees_with_local_models

/-- Forgetting the canonical cover metric retains the canonical continuation cover.

%%handwave
name: Forgetting the canonical cover metric preserves the canonical cover
statement: When canonical-cover-metric continuation fields are viewed as general fields, their simply connected cover is the canonical path-homotopy cover.
proof: This is the cover selected by the conversion.
-/
@[simp]
theorem toHyperbolicDevelopingContinuationDataFields_cover
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetric
        x₀ g localModels) :
    F.toHyperbolicDevelopingContinuationDataFields.cover =
      canonicalContinuationCover x₀ :=
  rfl

/-- Forgetting the canonical cover metric retains that metric on the underlying cover.

%%handwave
name: Forgetting the canonical cover metric preserves that metric
statement: The metric retained by the underlying continuation fields is the canonical pullback metric on the path-homotopy cover.
proof: The conversion copies the canonical cover metric into the general cover-metric field.
-/
@[simp]
theorem toHyperbolicDevelopingContinuationDataFields_coverMetric
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetric
        x₀ g localModels) :
    F.toHyperbolicDevelopingContinuationDataFields.coverMetric =
      canonicalContinuationCoverMetric x₀ g :=
  rfl

end HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetric

/--
On the canonical path-homotopy cover, local agreement with hyperbolic local
models forces chartwise holomorphicity of the continued map.

%%handwave
name: Canonical local-model agreement makes the developing map holomorphic
statement: Let $dev:X̃→ℍ$ on the canonical path-homotopy cover agree locally with Möbius-transformed hyperbolic charts. Then $dev$ is holomorphic in the complex charts of $X̃$.
proof: Near each lift, write $dev$ as a real Möbius action after a hyperbolic chart and the holomorphic covering projection. Each factor is holomorphic, so the local coordinate expression is complex differentiable.
-/
theorem canonicalAgreement_dev_holomorphic
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalModels localModels
        (canonicalContinuationCover x₀) dev) :
    HyperbolicDevelopingMapHolomorphic (canonicalContinuationCover x₀) dev := by
  intro y
  classical
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let e : OpenPartialHomeomorph (canonicalContinuationCover x₀).total ℂ :=
    chartAt ℂ y
  let z₀ : ℂ := e y
  let xᵧ : X := (canonicalContinuationCover x₀).projection y
  have hz₀_target : z₀ ∈ e.target := by
    dsimp [z₀, e]
    exact mem_chart_target ℂ y
  have hsymm_z₀ : e.symm z₀ = y := by
    dsimp [z₀, e]
    exact (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hy_domain : xᵧ ∈ (localModels.chartAt x).domain := by
    dsimp [xᵧ]
    exact hdomain y hyU
  have hz₀_base :
      z₀ = (chartAt ℂ xᵧ) xᵧ := by
    dsimp [z₀, e, xᵧ, canonicalContinuationCover]
    exact
      PathHomotopyUniversalCover.chartAt_apply_eq_chartAt_endpoint_apply
        (x₀ := x₀) y y (mem_chart_source ℂ y)
  have hlocal :
      DifferentiableAt ℂ
        (fun z : ℂ =>
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((chartAt ℂ xᵧ).symm z)) : ℂ))
        z₀ := by
    have hlocal_base :
        DifferentiableAt ℂ
          (fun z : ℂ =>
            (realMobiusRepresentativeAction A
              ((localModels.chartAt x).toUpperHalfPlane
                ((chartAt ℂ xᵧ).symm z)) : ℂ))
          ((chartAt ℂ xᵧ) xᵧ) :=
      (localModels.chartAt x).realMobius_postcomp_coordinateExpressionAt_differentiableAt
        A hy_domain
    simpa [hz₀_base] using hlocal_base
  have hUpre : e.symm ⁻¹' U ∈ nhds z₀ :=
    (e.continuousAt_symm hz₀_target).preimage_mem_nhds
      (by simpa [hsymm_z₀] using hUopen.mem_nhds hyU)
  have htarget : e.target ∈ nhds z₀ :=
    e.open_target.mem_nhds hz₀_target
  have heq :
      (fun z : ℂ => (dev (e.symm z) : ℂ)) =ᶠ[nhds z₀]
        (fun z : ℂ =>
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((chartAt ℂ xᵧ).symm z)) : ℂ)) := by
    filter_upwards [htarget, hUpre] with z hz_target hzU
    have hprojection :
        (canonicalContinuationCover x₀).projection (e.symm z) =
          (chartAt ℂ xᵧ).symm z := by
      dsimp [e, xᵧ, canonicalContinuationCover]
      exact
        PathHomotopyUniversalCover.endpoint_chartAt_symm_eq_chartAt_endpoint_symm
          (x₀ := x₀) y hz_target
    calc
      (dev (e.symm z) : ℂ) =
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((canonicalContinuationCover x₀).projection (e.symm z))) : ℂ) := by
        rw [hagree (e.symm z) hzU]
      _ =
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((chartAt ℂ xᵧ).symm z)) : ℂ) := by
        rw [hprojection]
  exact hlocal.congr_of_eventuallyEq heq

/--
Real-Mobius postcomposition of a local model has nonzero derivative in the
ambient surface coordinate.

%%handwave
name: A Möbius-transformed hyperbolic chart has nonzero coordinate derivative
statement: Let $U$ be a hyperbolic local chart, $A$ a real Möbius representative, and $x∈U$. The derivative at the ambient coordinate of $x$ of $z↦A·U((chart_x)^{-1}(z))$ is nonzero.
proof: The local hyperbolic coordinate has nonzero derivative, and the real Möbius action has nonzero complex derivative on $ℍ$. The chain rule makes their product nonzero.
-/
theorem hyperbolicLocalChart_realMobius_postcomp_coordinateExpressionAt_deriv_ne_zero
    {g : HyperbolicMetric X} (U : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) {x₀ : X} (hx₀ : x₀ ∈ U.domain) :
    deriv
      (fun z : ℂ =>
        (realMobiusRepresentativeAction A
          (U.toUpperHalfPlane ((chartAt ℂ x₀).symm z)) : ℂ))
      ((chartAt ℂ x₀) x₀) ≠ 0 := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  let z₀ : ℂ := e x₀
  let F : ℂ → ℂ := fun z => (U.toUpperHalfPlane (e.symm z) : ℂ)
  let M : ℂ → ℂ := fun w =>
    (realMobiusRepresentativeAction A (UpperHalfPlane.ofComplex w) : ℂ)
  have hsymm_z₀ : e.symm z₀ = x₀ := by
    dsimp [z₀, e]
    exact (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)
  have hF_point : F z₀ = (U.toUpperHalfPlane x₀ : ℂ) := by
    dsimp [F]
    rw [hsymm_z₀]
  have hF_diff : DifferentiableAt ℂ F z₀ := by
    simpa [F, e, z₀] using U.coordinateExpressionAt_differentiableAt hx₀
  have hM_diff :
      DifferentiableAt ℂ M (U.toUpperHalfPlane x₀ : ℂ) := by
    simpa [M] using
      realMobiusRepresentativeAction_differentiableAt A
        (U.toUpperHalfPlane x₀)
  have hF_deriv_ne : deriv F z₀ ≠ 0 := by
    have hne :=
      (hyperbolicLocalChart_pullbackSquaredDensityFormulaAt U hx₀).coordinateDerivative_ne_zero
        hx₀
    simpa [F, e, z₀, hyperbolicLocalChartCoordinateDerivativeAt] using hne
  have hM_deriv_ne : deriv M (U.toUpperHalfPlane x₀ : ℂ) ≠ 0 := by
    simpa [M] using
      realMobiusRepresentativeAction_standardChart_deriv_ne_zero A
        (U.toUpperHalfPlane x₀)
  have hchain :
      deriv
        (fun z : ℂ =>
          (realMobiusRepresentativeAction A
            (U.toUpperHalfPlane (e.symm z)) : ℂ))
        z₀ =
        deriv M (U.toUpperHalfPlane x₀ : ℂ) * deriv F z₀ := by
    have hcomp :=
      deriv_comp_of_eq z₀ hM_diff hF_diff hF_point
    calc
      deriv
        (fun z : ℂ =>
          (realMobiusRepresentativeAction A
            (U.toUpperHalfPlane (e.symm z)) : ℂ))
        z₀ =
          deriv (fun z : ℂ => M (F z)) z₀ := by
            congr 1
            ext z
            simp [M, F]
      _ = deriv M (U.toUpperHalfPlane x₀ : ℂ) * deriv F z₀ := by
            simpa [Function.comp_def, hF_point] using hcomp
  dsimp [e, z₀] at hchain
  rw [hchain]
  exact mul_ne_zero hM_deriv_ne hF_deriv_ne

/--
A local hyperbolic chart, after real-Mobius postcomposition, satisfies the
concrete chartwise pullback-metric identity at the base point.

This is the metric analogue of the local regularity lemmas above: the witness
is the actual ambient coordinate expression, restricted to the part of the
coordinate chart landing in the local-model domain.

%%handwave
name: A Möbius-transformed hyperbolic chart pulls back the Poincaré metric
statement: For a hyperbolic local chart $U$, real Möbius representative $A$, and $x∈U$, the map $z↦A·U(z)$ pulls the Poincaré conformal metric back to $g$ at $x$ in the ambient source chart and any target chart.
proof: The hyperbolic chart pulls the Poincaré metric back to $g$, while the real Möbius action preserves the Poincaré metric. Compose the two chartwise pullback identities.
-/
theorem hyperbolicLocalChart_realMobius_postcomp_pullsBackMetricInChartsAt_chartAt
    {g : HyperbolicMetric X} (U : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) {x₀ : X} (hx₀ : x₀ ∈ U.domain)
    (targetChart : OpenPartialHomeomorph ℍ ℂ)
    (targetChart_mem_atlas : targetChart ∈ atlas ℂ ℍ) :
    PullsBackMetricInChartsAt
      (fun x : X => realMobiusRepresentativeAction A (U.toUpperHalfPlane x))
      upperHalfPlaneConformalMetric g.toConformalMetric
      (chartAt ℂ x₀) (chart_mem_atlas ℂ x₀)
      targetChart targetChart_mem_atlas x₀ := by
  intro hx₀_source _himage
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  let z₀ : ℂ := e x₀
  let c : OpenPartialHomeomorph ℍ ℂ :=
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      UpperHalfPlane.coe UpperHalfPlane.isOpenEmbedding_coe
  have htarget_eq : targetChart = c := by
    simpa [c] using targetChart_mem_atlas
  subst targetChart
  let localMap : ℂ → ℂ := fun z =>
    (realMobiusRepresentativeAction A
      (U.toUpperHalfPlane (e.symm z)) : ℂ)
  let coordDomain : Set ℂ := e.target ∩ e.symm ⁻¹' U.domain
  have hz₀_target : z₀ ∈ e.target := by
    dsimp [z₀, e]
    exact e.map_source hx₀_source
  have hsymm_z₀ : e.symm z₀ = x₀ := by
    dsimp [z₀, e]
    exact e.left_inv hx₀_source
  refine
    ⟨coordDomain, localMap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact e.isOpen_inter_preimage_symm U.isOpen_domain
  · refine ⟨hz₀_target, ?_⟩
    change e.symm z₀ ∈ U.domain
    rw [hsymm_z₀]
    exact hx₀
  · intro z hz
    exact hz.1
  · intro z hz
    exact e.map_target hz.1
  · intro z _hz
    simp
  · intro z _hz
    simpa [localMap, c] using
      (mem_chart_target ℂ
        (realMobiusRepresentativeAction A
          (U.toUpperHalfPlane (e.symm z))))
  · intro z _hz
    simp [localMap, e]
  · simpa [localMap, e, z₀] using
      U.realMobius_postcomp_coordinateExpressionAt_differentiableAt A hx₀
  · let F : ℂ → ℂ := fun z => (U.toUpperHalfPlane (e.symm z) : ℂ)
    let M : ℂ → ℂ := fun w =>
      (realMobiusRepresentativeAction A (UpperHalfPlane.ofComplex w) : ℂ)
    let p : ℍ := U.toUpperHalfPlane x₀
    have hF_point : F z₀ = (p : ℂ) := by
      dsimp [F, p]
      rw [hsymm_z₀]
    have hF_diff : DifferentiableAt ℂ F z₀ := by
      simpa [F, e, z₀] using U.coordinateExpressionAt_differentiableAt hx₀
    have hM_diff : DifferentiableAt ℂ M (p : ℂ) := by
      simpa [M, p] using realMobiusRepresentativeAction_differentiableAt A p
    have hchain :
        deriv localMap z₀ = deriv M (p : ℂ) * deriv F z₀ := by
      have hcomp := deriv_comp_of_eq z₀ hM_diff hF_diff hF_point
      calc
        deriv localMap z₀ = deriv (fun z : ℂ => M (F z)) z₀ := by
          congr 1
          ext z
          simp [localMap, M, F]
        _ = deriv M (p : ℂ) * deriv F z₀ := by
          simpa [Function.comp_def, hF_point] using hcomp
    have hnorm :
        Complex.normSq (deriv localMap z₀) =
          Complex.normSq (deriv M (p : ℂ)) *
            Complex.normSq (deriv F z₀) := by
      rw [hchain]
      exact Complex.normSq_mul _ _
    have hlocalPull := hyperbolicLocalChart_pullbackSquaredDensityFormulaAt U hx₀
    have hsource :
        g.toConformalMetric.densitySqInChart e (chart_mem_atlas ℂ x₀) z₀ =
          ((p : ℂ).im ^ 2)⁻¹ * Complex.normSq (deriv F z₀) := by
      calc
        g.toConformalMetric.densitySqInChart e (chart_mem_atlas ℂ x₀) z₀ =
            Complex.normSq (deriv F z₀) / ((p : ℂ).im ^ 2) := by
          simpa [F, e, z₀, p, hyperbolicLocalChartCoordinateDerivativeAt,
            hyperbolicLocalChartCoordinateExpressionAt,
            hyperbolicLocalChartCoordinateDensitySqAt] using hlocalPull.symm
        _ = ((p : ℂ).im ^ 2)⁻¹ * Complex.normSq (deriv F z₀) := by
          rw [div_eq_mul_inv, mul_comm]
    have hmobius :
        ((p : ℂ).im ^ 2)⁻¹ =
          ((realMobiusRepresentativeAction A p : ℂ).im ^ 2)⁻¹ *
            Complex.normSq (deriv M (p : ℂ)) := by
      have hmetric := realMobiusRepresentativeAction_deriv_hyperbolicNormSq A p
      calc
        ((p : ℂ).im ^ 2)⁻¹ =
            Complex.normSq (deriv M (p : ℂ)) /
              ((realMobiusRepresentativeAction A p : ℂ).im ^ 2) := by
          simpa [one_div, M] using hmetric.symm
        _ =
            ((realMobiusRepresentativeAction A p : ℂ).im ^ 2)⁻¹ *
              Complex.normSq (deriv M (p : ℂ)) := by
          rw [div_eq_mul_inv, mul_comm]
    have hmetric_final :
        g.toConformalMetric.densitySqInChart e (chart_mem_atlas ℂ x₀) z₀ =
          ((realMobiusRepresentativeAction A p : ℂ).im ^ 2)⁻¹ *
            Complex.normSq (deriv localMap z₀) := by
      calc
        g.toConformalMetric.densitySqInChart e (chart_mem_atlas ℂ x₀) z₀ =
            ((p : ℂ).im ^ 2)⁻¹ * Complex.normSq (deriv F z₀) := hsource
        _ =
            (((realMobiusRepresentativeAction A p : ℂ).im ^ 2)⁻¹ *
                Complex.normSq (deriv M (p : ℂ))) *
              Complex.normSq (deriv F z₀) := by
          rw [hmobius]
        _ =
            ((realMobiusRepresentativeAction A p : ℂ).im ^ 2)⁻¹ *
              (Complex.normSq (deriv M (p : ℂ)) *
                Complex.normSq (deriv F z₀)) := by
          ring
        _ =
            ((realMobiusRepresentativeAction A p : ℂ).im ^ 2)⁻¹ *
              Complex.normSq (deriv localMap z₀) := by
          rw [hnorm]
    simpa [upperHalfPlaneConformalMetric, poincareDensitySqInChart,
      localMap, e, z₀, p, hsymm_z₀, c] using hmetric_final

/--
On the canonical cover, local agreement with hyperbolic local models gives the
actual chartwise pullback-metric identity for the continued developing map in
the canonical `chartAt` coordinate.

The proof composes the local model's Poincare pullback formula with the
already-proved canonical projection pullback formula, then transfers across
the local equality between `dev` and the Mobius-postcomposed local model.

%%handwave
name: Canonical local agreement gives the metric identity in the canonical source chart
statement: If $dev$ agrees locally with the hyperbolic models on the canonical cover, then at every lift $y$ and in the canonical source chart, $dev^*g_{ℍ}=g̃$ in any upper-half-plane target chart.
proof: Near $y$, replace $dev$ by a Möbius-transformed local model. Compose the model’s Poincaré pullback identity with the covering projection’s pullback of $g$, then transfer the result across the local equality.
-/
theorem canonicalAgreement_dev_pullsBackMetricInChartsAt_chartAt
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalModels localModels
        (canonicalContinuationCover x₀) dev)
    (y : (canonicalContinuationCover x₀).total)
    (targetChart : OpenPartialHomeomorph ℍ ℂ)
    (targetChart_mem_atlas : targetChart ∈ atlas ℂ ℍ) :
    PullsBackMetricInChartsAt dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g)
      (chartAt ℂ y) (chart_mem_atlas ℂ y)
      targetChart targetChart_mem_atlas y := by
  classical
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let localChart : HyperbolicLocalChart X g := localModels.chartAt x
  let localModelOnBase : X → ℍ := fun x' =>
    realMobiusRepresentativeAction A (localChart.toUpperHalfPlane x')
  let localModelOnCover : (canonicalContinuationCover x₀).total → ℍ := fun y' =>
    localModelOnBase ((canonicalContinuationCover x₀).projection y')
  have hy_domain :
      (canonicalContinuationCover x₀).projection y ∈ localChart.domain := by
    exact hdomain y hyU
  have hprojection_chart :
      (canonicalContinuationCover x₀).projection y ∈
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y)).source :=
    mem_chart_source ℂ ((canonicalContinuationCover x₀).projection y)
  have hbase :
      PullsBackMetricInChartsAt localModelOnBase upperHalfPlaneConformalMetric
        g.toConformalMetric
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
        (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
        targetChart targetChart_mem_atlas
        ((canonicalContinuationCover x₀).projection y) := by
    simpa [localModelOnBase, localChart] using
      hyperbolicLocalChart_realMobius_postcomp_pullsBackMetricInChartsAt_chartAt
        (X := X) localChart A hy_domain targetChart targetChart_mem_atlas
  have hprojection_pullback :
      PullsBackMetricInChartsAt
        (canonicalContinuationCover x₀).projection
        g.toConformalMetric
        (canonicalContinuationCoverMetric x₀ g)
        (chartAt ℂ y) (chart_mem_atlas ℂ y)
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
        (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
        y :=
    (canonicalContinuationCoverMetric_pullback x₀ g).in_charts_at
      (chartAt ℂ y) (chart_mem_atlas ℂ y)
      (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
      (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
      y
  have hlocalModel :
      PullsBackMetricInChartsAt localModelOnCover upperHalfPlaneConformalMetric
        (canonicalContinuationCoverMetric x₀ g)
        (chartAt ℂ y) (chart_mem_atlas ℂ y)
        targetChart targetChart_mem_atlas y := by
    simpa [localModelOnCover, localModelOnBase] using
      PullsBackMetricInChartsAt.comp
        (F := localModelOnBase)
        (G := (canonicalContinuationCover x₀).projection)
        hprojection_chart hbase hprojection_pullback
  have heq : localModelOnCover =ᶠ[nhds y] dev := by
    filter_upwards [hUopen.mem_nhds hyU] with y' hy'
    exact (hagree y' hy').symm
  exact PullsBackMetricInChartsAt.congr_of_eventuallyEq_nhds hlocalModel heq

/--
On the canonical cover, local agreement with hyperbolic local models gives the
actual chartwise pullback-metric identity for the continued developing map in
any source chart.

%%handwave
name: Canonical local agreement gives the metric identity in every source chart
statement: Under canonical local-model agreement, the chartwise identity $dev^*g_{ℍ}=g̃$ holds at every lift for every compatible source chart and every upper-half-plane target chart.
proof: First prove the identity in the canonical source chart, then use invariance of the chartwise pullback relation under changing source charts in the same complex atlas.
-/
theorem canonicalAgreement_dev_pullsBackMetricInChartsAt
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalModels localModels
        (canonicalContinuationCover x₀) dev)
    (sourceChart : OpenPartialHomeomorph (canonicalContinuationCover x₀).total ℂ)
    (sourceChart_mem_atlas :
      sourceChart ∈ atlas ℂ (canonicalContinuationCover x₀).total)
    (targetChart : OpenPartialHomeomorph ℍ ℂ)
    (targetChart_mem_atlas : targetChart ∈ atlas ℂ ℍ)
    (y : (canonicalContinuationCover x₀).total) :
    PullsBackMetricInChartsAt dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g)
      sourceChart sourceChart_mem_atlas
      targetChart targetChart_mem_atlas y := by
  classical
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let localChart : HyperbolicLocalChart X g := localModels.chartAt x
  let localModelOnBase : X → ℍ := fun x' =>
    realMobiusRepresentativeAction A (localChart.toUpperHalfPlane x')
  let localModelOnCover : (canonicalContinuationCover x₀).total → ℍ := fun y' =>
    localModelOnBase ((canonicalContinuationCover x₀).projection y')
  have hy_domain :
      (canonicalContinuationCover x₀).projection y ∈ localChart.domain := by
    exact hdomain y hyU
  have hprojection_chart :
      (canonicalContinuationCover x₀).projection y ∈
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y)).source :=
    mem_chart_source ℂ ((canonicalContinuationCover x₀).projection y)
  have hbase :
      PullsBackMetricInChartsAt localModelOnBase upperHalfPlaneConformalMetric
        g.toConformalMetric
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
        (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
        targetChart targetChart_mem_atlas
        ((canonicalContinuationCover x₀).projection y) := by
    simpa [localModelOnBase, localChart] using
      hyperbolicLocalChart_realMobius_postcomp_pullsBackMetricInChartsAt_chartAt
        (X := X) localChart A hy_domain targetChart targetChart_mem_atlas
  have hprojection_pullback :
      PullsBackMetricInChartsAt
        (canonicalContinuationCover x₀).projection
        g.toConformalMetric
        (canonicalContinuationCoverMetric x₀ g)
        sourceChart sourceChart_mem_atlas
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
        (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
        y :=
    (canonicalContinuationCoverMetric_pullback x₀ g).in_charts_at
      sourceChart sourceChart_mem_atlas
      (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
      (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
      y
  have hlocalModel :
      PullsBackMetricInChartsAt localModelOnCover upperHalfPlaneConformalMetric
        (canonicalContinuationCoverMetric x₀ g)
        sourceChart sourceChart_mem_atlas
        targetChart targetChart_mem_atlas y := by
    simpa [localModelOnCover, localModelOnBase] using
      PullsBackMetricInChartsAt.comp
        (F := localModelOnBase)
        (G := (canonicalContinuationCover x₀).projection)
        hprojection_chart hbase hprojection_pullback
  have heq : localModelOnCover =ᶠ[nhds y] dev := by
    filter_upwards [hUopen.mem_nhds hyU] with y' hy'
    exact (hagree y' hy').symm
  exact PullsBackMetricInChartsAt.congr_of_eventuallyEq_nhds hlocalModel heq

/--
Local agreement with hyperbolic local models supplies the full pullback metric
identity for the continued developing map on the canonical cover.

%%handwave
name: Canonical local agreement makes the developing map a local Poincaré isometry
statement: If $dev$ on the canonical cover agrees locally with Möbius-transformed hyperbolic charts, then $dev^*g_{ℍ}=g̃$ globally.
proof: For arbitrary source and target charts and any point, apply the chartwise metric identity established from local agreement.
-/
theorem canonicalAgreement_dev_pullsBackMetric
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalModels localModels
        (canonicalContinuationCover x₀) dev) :
    PullsBackMetric dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g) where
  in_charts := by
    intro sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas y
    exact canonicalAgreement_dev_pullsBackMetricInChartsAt
      h sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas y

/--
On the canonical path-homotopy cover, local agreement with hyperbolic local
models forces the nonzero-derivative part of developing-map regularity.

%%handwave
name: Canonical local agreement gives a nonvanishing developing-map derivative
statement: If $dev$ on the canonical cover agrees locally with hyperbolic local models, then its complex coordinate derivative is nonzero at every lift.
proof: Use the local equality with a Möbius-transformed hyperbolic chart. Its coordinate derivative is nonzero, and equality on a neighborhood identifies this derivative with that of $dev$.
-/
theorem canonicalAgreement_dev_local_biholomorphic
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalModels localModels
        (canonicalContinuationCover x₀) dev) :
    HyperbolicDevelopingMapLocallyBiholomorphic
      (canonicalContinuationCover x₀) dev := by
  intro y
  classical
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let e : OpenPartialHomeomorph (canonicalContinuationCover x₀).total ℂ :=
    chartAt ℂ y
  let z₀ : ℂ := e y
  let xᵧ : X := (canonicalContinuationCover x₀).projection y
  have hz₀_target : z₀ ∈ e.target := by
    dsimp [z₀, e]
    exact mem_chart_target ℂ y
  have hsymm_z₀ : e.symm z₀ = y := by
    dsimp [z₀, e]
    exact (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hy_domain : xᵧ ∈ (localModels.chartAt x).domain := by
    dsimp [xᵧ]
    exact hdomain y hyU
  have hz₀_base :
      z₀ = (chartAt ℂ xᵧ) xᵧ := by
    dsimp [z₀, e, xᵧ, canonicalContinuationCover]
    exact
      PathHomotopyUniversalCover.chartAt_apply_eq_chartAt_endpoint_apply
        (x₀ := x₀) y y (mem_chart_source ℂ y)
  have hlocal_deriv_ne :
      deriv
        (fun z : ℂ =>
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((chartAt ℂ xᵧ).symm z)) : ℂ))
        z₀ ≠ 0 := by
    have hlocal_base :=
      hyperbolicLocalChart_realMobius_postcomp_coordinateExpressionAt_deriv_ne_zero
        (localModels.chartAt x) A hy_domain
    simpa [hz₀_base] using hlocal_base
  have hUpre : e.symm ⁻¹' U ∈ nhds z₀ :=
    (e.continuousAt_symm hz₀_target).preimage_mem_nhds
      (by simpa [hsymm_z₀] using hUopen.mem_nhds hyU)
  have htarget : e.target ∈ nhds z₀ :=
    e.open_target.mem_nhds hz₀_target
  have heq :
      HyperbolicDevelopingMapCoordinateExpression
          (canonicalContinuationCover x₀) dev y =ᶠ[nhds z₀]
        (fun z : ℂ =>
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((chartAt ℂ xᵧ).symm z)) : ℂ)) := by
    filter_upwards [htarget, hUpre] with z hz_target hzU
    have hprojection :
        (canonicalContinuationCover x₀).projection (e.symm z) =
          (chartAt ℂ xᵧ).symm z := by
      dsimp [e, xᵧ, canonicalContinuationCover]
      exact
        PathHomotopyUniversalCover.endpoint_chartAt_symm_eq_chartAt_endpoint_symm
          (x₀ := x₀) y hz_target
    calc
      HyperbolicDevelopingMapCoordinateExpression
          (canonicalContinuationCover x₀) dev y z =
          (dev (e.symm z) : ℂ) := by
        rfl
      _ =
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((canonicalContinuationCover x₀).projection (e.symm z))) : ℂ) := by
        rw [hagree (e.symm z) hzU]
      _ =
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((chartAt ℂ xᵧ).symm z)) : ℂ) := by
        rw [hprojection]
  have hderiv_eq :=
    Filter.EventuallyEq.deriv_eq heq
  rw [hderiv_eq]
  exact hlocal_deriv_ne

/--
An analytic one-variable complex map with nonzero derivative has the concrete
local-homeomorphism branch data required by developing-map regularity.

%%handwave
name: A holomorphic function with nonzero derivative has a local biholomorphic branch
statement: Let $f:ℂ→ℂ$ be analytic at $z_0$, with $f′(z_0)≠0$, and let $S$ be a neighborhood of $z_0$. Then there is an open partial homeomorphism branch through $z_0$, contained in $S$, equal to $f$ on its source, differentiable there, and with nonzero derivative throughout.
proof: Apply the holomorphic inverse function theorem at $z_0$, then shrink the source by intersecting with $S$ and with a neighborhood on which the derivative remains nonzero.
-/
theorem analyticAt_local_biholomorphism_branch
    {f : ℂ → ℂ} {z₀ : ℂ} {S : Set ℂ}
    (hf : AnalyticAt ℂ f z₀) (hderiv : deriv f z₀ ≠ 0)
    (hS : S ∈ nhds z₀) :
    ∃ branch : OpenPartialHomeomorph ℂ ℂ,
      z₀ ∈ branch.source ∧
        branch.source ⊆ S ∧
        ∀ z ∈ branch.source,
          branch z = f z ∧ DifferentiableAt ℂ branch z ∧ deriv branch z ≠ 0 := by
  classical
  let hstrict : HasStrictDerivAt f (deriv f z₀) z₀ :=
    hf.hasStrictDerivAt
  let e₀ : OpenPartialHomeomorph ℂ ℂ :=
    (hstrict.hasStrictFDerivAt_equiv hderiv).toOpenPartialHomeomorph f
  have hz₀e₀ : z₀ ∈ e₀.source :=
    (hstrict.hasStrictFDerivAt_equiv hderiv).mem_toOpenPartialHomeomorph_source
  have hdiff_event :
      ∀ᶠ z in nhds z₀, DifferentiableAt ℂ f z :=
    hf.eventually_analyticAt.mono fun z hz => hz.differentiableAt
  have hderiv_event :
      ∀ᶠ z in nhds z₀, deriv f z ≠ 0 :=
    hf.deriv.continuousAt.eventually_ne hderiv
  rcases mem_nhds_iff.mp hS with ⟨S₀, hS₀_sub, hS₀_open, hz₀S₀⟩
  rcases eventually_nhds_iff.mp (hdiff_event.and hderiv_event) with
    ⟨W, hW, hWopen, hz₀W⟩
  let branch : OpenPartialHomeomorph ℂ ℂ := e₀.restrOpen (W ∩ S₀) (hWopen.inter hS₀_open)
  refine ⟨branch, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hz₀e₀, hz₀W, hz₀S₀⟩
  · intro z hz
    have hz' : z ∈ e₀.source ∩ (W ∩ S₀) := by
      simpa [branch, OpenPartialHomeomorph.restrOpen_source] using hz
    exact hS₀_sub hz'.2.2
  · intro z hz
    have hz' : z ∈ e₀.source ∩ (W ∩ S₀) := by
      simpa [branch, OpenPartialHomeomorph.restrOpen_source] using hz
    have hz_props := hW z hz'.2.1
    refine ⟨?_, ?_, ?_⟩
    · simp [branch, e₀]
    · simpa [branch, e₀] using hz_props.1
    · simpa [branch, e₀] using hz_props.2

/--
On the canonical path-homotopy cover, local agreement with local models makes
the developing-map coordinate expression analytic at every point.

%%handwave
name: Canonical local agreement makes every developing coordinate expression analytic
statement: Under canonical local-model agreement, for every lift $y$ the complex coordinate expression of $dev$ is analytic at the source coordinate of $y$.
proof: The chartwise holomorphicity theorem gives complex differentiability on a neighborhood of the point; package this local differentiability as analyticity at the point.
-/
theorem canonicalAgreement_dev_coordinateExpression_analyticAt
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalModels localModels
        (canonicalContinuationCover x₀) dev)
    (y : (canonicalContinuationCover x₀).total) :
    AnalyticAt ℂ
      (HyperbolicDevelopingMapCoordinateExpression
        (canonicalContinuationCover x₀) dev y)
      ((chartAt ℂ y) y) := by
  classical
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let e : OpenPartialHomeomorph (canonicalContinuationCover x₀).total ℂ :=
    chartAt ℂ y
  let z₀ : ℂ := e y
  let xᵧ : X := (canonicalContinuationCover x₀).projection y
  let b : OpenPartialHomeomorph X ℂ := chartAt ℂ xᵧ
  let localExpr : ℂ → ℂ := fun z =>
    (realMobiusRepresentativeAction A
      ((localModels.chartAt x).toUpperHalfPlane (b.symm z)) : ℂ)
  have hz₀_target : z₀ ∈ e.target := by
    dsimp [z₀, e]
    exact mem_chart_target ℂ y
  have hsymm_z₀ : e.symm z₀ = y := by
    dsimp [z₀, e]
    exact (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hy_domain : xᵧ ∈ (localModels.chartAt x).domain := by
    dsimp [xᵧ]
    exact hdomain y hyU
  have hz₀_base :
      z₀ = b xᵧ := by
    dsimp [z₀, e, xᵧ, b, canonicalContinuationCover]
    exact
      PathHomotopyUniversalCover.chartAt_apply_eq_chartAt_endpoint_apply
        (x₀ := x₀) y y (mem_chart_source ℂ y)
  have hbtarget : b xᵧ ∈ b.target := by
    dsimp [b]
    exact mem_chart_target ℂ xᵧ
  have hb_symm :
      b.symm (b xᵧ) = xᵧ := by
    dsimp [b]
    exact (chartAt ℂ xᵧ).left_inv (mem_chart_source ℂ xᵧ)
  let s : Set ℂ := b.target ∩ b.symm ⁻¹' (localModels.chartAt x).domain
  have hs_nhds : s ∈ nhds z₀ := by
    have htarget : b.target ∈ nhds (b xᵧ) :=
      b.open_target.mem_nhds hbtarget
    have hpre :
        b.symm ⁻¹' (localModels.chartAt x).domain ∈ nhds (b xᵧ) :=
      (b.continuousAt_symm hbtarget).preimage_mem_nhds
        (by simpa [hb_symm] using
          (localModels.chartAt x).isOpen_domain.mem_nhds hy_domain)
    simpa [s, hz₀_base] using Filter.inter_mem htarget hpre
  have hlocal_diffOn : DifferentiableOn ℂ localExpr s := by
    intro z hz
    have hz_target : z ∈ b.target := hz.1
    have hz_domain : b.symm z ∈ (localModels.chartAt x).domain := hz.2
    exact
      ((localModels.chartAt x).realMobius_postcomp_coordinateExpression_differentiableAt
        A b (chart_mem_atlas ℂ xᵧ) hz_target hz_domain).differentiableWithinAt
  have hlocal_analytic : AnalyticAt ℂ localExpr z₀ :=
    hlocal_diffOn.analyticAt hs_nhds
  have hUpre : e.symm ⁻¹' U ∈ nhds z₀ :=
    (e.continuousAt_symm hz₀_target).preimage_mem_nhds
      (by simpa [hsymm_z₀] using hUopen.mem_nhds hyU)
  have htarget : e.target ∈ nhds z₀ :=
    e.open_target.mem_nhds hz₀_target
  have heq :
      HyperbolicDevelopingMapCoordinateExpression
          (canonicalContinuationCover x₀) dev y =ᶠ[nhds z₀]
        localExpr := by
    filter_upwards [htarget, hUpre] with z hz_target hzU
    have hprojection :
        (canonicalContinuationCover x₀).projection (e.symm z) =
          b.symm z := by
      dsimp [e, b, xᵧ, canonicalContinuationCover]
      exact
        PathHomotopyUniversalCover.endpoint_chartAt_symm_eq_chartAt_endpoint_symm
          (x₀ := x₀) y hz_target
    calc
      HyperbolicDevelopingMapCoordinateExpression
          (canonicalContinuationCover x₀) dev y z =
          (dev (e.symm z) : ℂ) := by
        rfl
      _ =
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((canonicalContinuationCover x₀).projection (e.symm z))) : ℂ) := by
        rw [hagree (e.symm z) hzU]
      _ = localExpr z := by
        dsimp [localExpr]
        rw [hprojection]
  exact hlocal_analytic.congr heq.symm

/--
On the canonical path-homotopy cover, local agreement with hyperbolic local
models supplies the concrete local-homeomorphism branch data.

%%handwave
name: Canonical local agreement supplies local biholomorphic branches
statement: If $dev$ on the canonical cover agrees locally with hyperbolic local models, then at every lift its coordinate expression agrees near that point with an open partial homeomorphism whose derivative never vanishes.
proof: The coordinate expression is analytic and has nonzero derivative at the point. Apply the analytic local-biholomorphism branch theorem, restricting its source to the coordinate-chart domain.
-/
theorem canonicalAgreement_dev_local_biholomorphism_data
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalModels localModels
        (canonicalContinuationCover x₀) dev) :
    HyperbolicDevelopingMapLocalBiholomorphismData
      (canonicalContinuationCover x₀) dev := by
  intro y
  exact analyticAt_local_biholomorphism_branch
    (canonicalAgreement_dev_coordinateExpression_analyticAt h y)
    (canonicalAgreement_dev_local_biholomorphic h y)
    ((chartAt ℂ y).open_target.mem_nhds (mem_chart_target ℂ y))

/--
On the canonical path-homotopy cover, local agreement with the hyperbolic
local models supplies the full developing-map regularity package.

%%handwave
name: Canonical local-model agreement supplies full developing-map regularity
statement: If $dev$ on the canonical cover agrees locally with hyperbolic local models, then it is continuous and holomorphic, has nonzero coordinate derivative everywhere, and admits concrete local biholomorphic branches.
proof: Combine continuity from local agreement, canonical-cover holomorphicity, nonvanishing of the local-model derivative, and the analytic inverse-function branches.
-/
theorem canonicalAgreement_dev_regular
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalModels localModels
        (canonicalContinuationCover x₀) dev) :
    HyperbolicDevelopingMapRegularity (canonicalContinuationCover x₀) dev where
  continuous := h.continuous
  chartwise_holomorphic := canonicalAgreement_dev_holomorphic h
  local_biholomorphic := canonicalAgreement_dev_local_biholomorphic h
  local_biholomorphism_data := canonicalAgreement_dev_local_biholomorphism_data h

/--
On the canonical path-homotopy cover, local agreement with local-transition
models makes the developing-map coordinate expression analytic at every point.

%%handwave
name: Local-transition agreement makes each developing coordinate expression analytic
statement: If $dev$ on the canonical cover agrees locally with local-transition hyperbolic charts, then for every lift $y$ its complex coordinate expression is analytic at the source coordinate of $y$.
proof: On a neighborhood of $y$, replace $dev$ by a Möbius-transformed local hyperbolic chart after projection. This composite is analytic in the canonical coordinates, and local equality transfers analyticity.
-/
theorem canonicalLocalTransitionAgreement_dev_coordinateExpression_analyticAt
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev)
    (y : (canonicalContinuationCover x₀).total) :
    AnalyticAt ℂ
      (HyperbolicDevelopingMapCoordinateExpression
        (canonicalContinuationCover x₀) dev y)
      ((chartAt ℂ y) y) := by
  classical
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let e : OpenPartialHomeomorph (canonicalContinuationCover x₀).total ℂ :=
    chartAt ℂ y
  let z₀ : ℂ := e y
  let xᵧ : X := (canonicalContinuationCover x₀).projection y
  let b : OpenPartialHomeomorph X ℂ := chartAt ℂ xᵧ
  let localExpr : ℂ → ℂ := fun z =>
    (realMobiusRepresentativeAction A
      ((localModels.chartAt x).toUpperHalfPlane (b.symm z)) : ℂ)
  have hz₀_target : z₀ ∈ e.target := by
    dsimp [z₀, e]
    exact mem_chart_target ℂ y
  have hsymm_z₀ : e.symm z₀ = y := by
    dsimp [z₀, e]
    exact (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hy_domain : xᵧ ∈ (localModels.chartAt x).domain := by
    dsimp [xᵧ]
    exact hdomain y hyU
  have hz₀_base :
      z₀ = b xᵧ := by
    dsimp [z₀, e, xᵧ, b, canonicalContinuationCover]
    exact
      PathHomotopyUniversalCover.chartAt_apply_eq_chartAt_endpoint_apply
        (x₀ := x₀) y y (mem_chart_source ℂ y)
  have hbtarget : b xᵧ ∈ b.target := by
    dsimp [b]
    exact mem_chart_target ℂ xᵧ
  have hb_symm :
      b.symm (b xᵧ) = xᵧ := by
    dsimp [b]
    exact (chartAt ℂ xᵧ).left_inv (mem_chart_source ℂ xᵧ)
  let s : Set ℂ := b.target ∩ b.symm ⁻¹' (localModels.chartAt x).domain
  have hs_nhds : s ∈ nhds z₀ := by
    have htarget : b.target ∈ nhds (b xᵧ) :=
      b.open_target.mem_nhds hbtarget
    have hpre :
        b.symm ⁻¹' (localModels.chartAt x).domain ∈ nhds (b xᵧ) :=
      (b.continuousAt_symm hbtarget).preimage_mem_nhds
        (by simpa [hb_symm] using
          (localModels.chartAt x).isOpen_domain.mem_nhds hy_domain)
    simpa [s, hz₀_base] using Filter.inter_mem htarget hpre
  have hlocal_diffOn : DifferentiableOn ℂ localExpr s := by
    intro z hz
    have hz_target : z ∈ b.target := hz.1
    have hz_domain : b.symm z ∈ (localModels.chartAt x).domain := hz.2
    exact
      ((localModels.chartAt x).realMobius_postcomp_coordinateExpression_differentiableAt
        A b (chart_mem_atlas ℂ xᵧ) hz_target hz_domain).differentiableWithinAt
  have hlocal_analytic : AnalyticAt ℂ localExpr z₀ :=
    hlocal_diffOn.analyticAt hs_nhds
  have hUpre : e.symm ⁻¹' U ∈ nhds z₀ :=
    (e.continuousAt_symm hz₀_target).preimage_mem_nhds
      (by simpa [hsymm_z₀] using hUopen.mem_nhds hyU)
  have htarget : e.target ∈ nhds z₀ :=
    e.open_target.mem_nhds hz₀_target
  have heq :
      HyperbolicDevelopingMapCoordinateExpression
          (canonicalContinuationCover x₀) dev y =ᶠ[nhds z₀]
        localExpr := by
    filter_upwards [htarget, hUpre] with z hz_target hzU
    have hprojection :
        (canonicalContinuationCover x₀).projection (e.symm z) =
          b.symm z := by
      dsimp [e, b, xᵧ, canonicalContinuationCover]
      exact
        PathHomotopyUniversalCover.endpoint_chartAt_symm_eq_chartAt_endpoint_symm
          (x₀ := x₀) y hz_target
    calc
      HyperbolicDevelopingMapCoordinateExpression
          (canonicalContinuationCover x₀) dev y z =
          (dev (e.symm z) : ℂ) := by
        rfl
      _ =
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((canonicalContinuationCover x₀).projection (e.symm z))) : ℂ) := by
        rw [hagree (e.symm z) hzU]
      _ = localExpr z := by
        dsimp [localExpr]
        rw [hprojection]
  exact hlocal_analytic.congr heq.symm

/--
On the canonical path-homotopy cover, local agreement with local-transition
models forces chartwise holomorphicity of the continued map.

%%handwave
name: Local-transition agreement makes the developing map holomorphic
statement: If $dev$ on the canonical cover agrees locally with local-transition models, then its coordinate expression is complex differentiable at every lift.
proof: Analyticity of the coordinate expression at each lift implies the required pointwise complex differentiability.
-/
theorem canonicalLocalTransitionAgreement_dev_holomorphic
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev) :
    HyperbolicDevelopingMapHolomorphic (canonicalContinuationCover x₀) dev := by
  intro y
  simpa [HyperbolicDevelopingMapCoordinateExpression] using
    (canonicalLocalTransitionAgreement_dev_coordinateExpression_analyticAt h y).differentiableAt

/--
On the canonical path-homotopy cover, local agreement with local-transition
models forces the nonzero-derivative part of developing-map regularity.

%%handwave
name: Local-transition agreement gives a nonvanishing developing derivative
statement: If $dev$ agrees locally with local-transition hyperbolic models on the canonical cover, then its coordinate derivative is nonzero at every lift.
proof: Use the local equality with a Möbius-transformed hyperbolic chart and the nonzero derivative of that model expression.
-/
theorem canonicalLocalTransitionAgreement_dev_local_biholomorphic
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev) :
    HyperbolicDevelopingMapLocallyBiholomorphic
      (canonicalContinuationCover x₀) dev := by
  intro y
  classical
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let e : OpenPartialHomeomorph (canonicalContinuationCover x₀).total ℂ :=
    chartAt ℂ y
  let z₀ : ℂ := e y
  let xᵧ : X := (canonicalContinuationCover x₀).projection y
  have hz₀_target : z₀ ∈ e.target := by
    dsimp [z₀, e]
    exact mem_chart_target ℂ y
  have hsymm_z₀ : e.symm z₀ = y := by
    dsimp [z₀, e]
    exact (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hy_domain : xᵧ ∈ (localModels.chartAt x).domain := by
    dsimp [xᵧ]
    exact hdomain y hyU
  have hz₀_base :
      z₀ = (chartAt ℂ xᵧ) xᵧ := by
    dsimp [z₀, e, xᵧ, canonicalContinuationCover]
    exact
      PathHomotopyUniversalCover.chartAt_apply_eq_chartAt_endpoint_apply
        (x₀ := x₀) y y (mem_chart_source ℂ y)
  have hlocal_deriv_ne :
      deriv
        (fun z : ℂ =>
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((chartAt ℂ xᵧ).symm z)) : ℂ))
        z₀ ≠ 0 := by
    have hlocal_base :=
      hyperbolicLocalChart_realMobius_postcomp_coordinateExpressionAt_deriv_ne_zero
        (localModels.chartAt x) A hy_domain
    simpa [hz₀_base] using hlocal_base
  have hUpre : e.symm ⁻¹' U ∈ nhds z₀ :=
    (e.continuousAt_symm hz₀_target).preimage_mem_nhds
      (by simpa [hsymm_z₀] using hUopen.mem_nhds hyU)
  have htarget : e.target ∈ nhds z₀ :=
    e.open_target.mem_nhds hz₀_target
  have heq :
      HyperbolicDevelopingMapCoordinateExpression
          (canonicalContinuationCover x₀) dev y =ᶠ[nhds z₀]
        (fun z : ℂ =>
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((chartAt ℂ xᵧ).symm z)) : ℂ)) := by
    filter_upwards [htarget, hUpre] with z hz_target hzU
    have hprojection :
        (canonicalContinuationCover x₀).projection (e.symm z) =
          (chartAt ℂ xᵧ).symm z := by
      dsimp [e, xᵧ, canonicalContinuationCover]
      exact
        PathHomotopyUniversalCover.endpoint_chartAt_symm_eq_chartAt_endpoint_symm
          (x₀ := x₀) y hz_target
    calc
      HyperbolicDevelopingMapCoordinateExpression
          (canonicalContinuationCover x₀) dev y z =
          (dev (e.symm z) : ℂ) := by
        rfl
      _ =
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((canonicalContinuationCover x₀).projection (e.symm z))) : ℂ) := by
        rw [hagree (e.symm z) hzU]
      _ =
          (realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane
              ((chartAt ℂ xᵧ).symm z)) : ℂ) := by
        rw [hprojection]
  have hderiv_eq :=
    Filter.EventuallyEq.deriv_eq heq
  rw [hderiv_eq]
  exact hlocal_deriv_ne

/--
On the canonical path-homotopy cover, local agreement with local-transition
models supplies the concrete local-homeomorphism branch data.

%%handwave
name: Local-transition agreement supplies local biholomorphic branches
statement: If $dev$ agrees locally with local-transition models, then around every lift its coordinate expression agrees with an open partial homeomorphism whose derivative is everywhere nonzero on the chosen source.
proof: Combine analytic coordinate expressions with their nonzero derivative and apply the analytic inverse-function branch theorem, shrinking inside the coordinate domain.
-/
theorem canonicalLocalTransitionAgreement_dev_local_biholomorphism_data
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev) :
    HyperbolicDevelopingMapLocalBiholomorphismData
      (canonicalContinuationCover x₀) dev := by
  intro y
  exact analyticAt_local_biholomorphism_branch
    (canonicalLocalTransitionAgreement_dev_coordinateExpression_analyticAt h y)
    (canonicalLocalTransitionAgreement_dev_local_biholomorphic h y)
    ((chartAt ℂ y).open_target.mem_nhds (mem_chart_target ℂ y))

/--
On the canonical cover, local agreement with local-transition models gives the
actual chartwise pullback-metric identity for the continued developing map in
the canonical `chartAt` coordinate.

%%handwave
name: Local-transition agreement gives the metric identity in canonical coordinates
statement: Under local-transition model agreement, at every canonical-cover point $y$ the map $dev$ pulls the Poincaré metric back to the canonical cover metric in the canonical source chart and any target chart.
proof: Use the local equality with a Möbius-transformed hyperbolic chart, compose its metric identity with the covering projection pullback, and transfer across the local equality.
-/
theorem canonicalLocalTransitionAgreement_dev_pullsBackMetricInChartsAt_chartAt
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev)
    (y : (canonicalContinuationCover x₀).total)
    (targetChart : OpenPartialHomeomorph ℍ ℂ)
    (targetChart_mem_atlas : targetChart ∈ atlas ℂ ℍ) :
    PullsBackMetricInChartsAt dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g)
      (chartAt ℂ y) (chart_mem_atlas ℂ y)
      targetChart targetChart_mem_atlas y := by
  classical
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let localChart : HyperbolicLocalChart X g := localModels.chartAt x
  let localModelOnBase : X → ℍ := fun x' =>
    realMobiusRepresentativeAction A (localChart.toUpperHalfPlane x')
  let localModelOnCover : (canonicalContinuationCover x₀).total → ℍ := fun y' =>
    localModelOnBase ((canonicalContinuationCover x₀).projection y')
  have hy_domain :
      (canonicalContinuationCover x₀).projection y ∈ localChart.domain := by
    exact hdomain y hyU
  have hprojection_chart :
      (canonicalContinuationCover x₀).projection y ∈
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y)).source :=
    mem_chart_source ℂ ((canonicalContinuationCover x₀).projection y)
  have hbase :
      PullsBackMetricInChartsAt localModelOnBase upperHalfPlaneConformalMetric
        g.toConformalMetric
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
        (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
        targetChart targetChart_mem_atlas
        ((canonicalContinuationCover x₀).projection y) := by
    simpa [localModelOnBase, localChart] using
      hyperbolicLocalChart_realMobius_postcomp_pullsBackMetricInChartsAt_chartAt
        (X := X) localChart A hy_domain targetChart targetChart_mem_atlas
  have hprojection_pullback :
      PullsBackMetricInChartsAt
        (canonicalContinuationCover x₀).projection
        g.toConformalMetric
        (canonicalContinuationCoverMetric x₀ g)
        (chartAt ℂ y) (chart_mem_atlas ℂ y)
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
        (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
        y :=
    (canonicalContinuationCoverMetric_pullback x₀ g).in_charts_at
      (chartAt ℂ y) (chart_mem_atlas ℂ y)
      (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
      (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
      y
  have hlocalModel :
      PullsBackMetricInChartsAt localModelOnCover upperHalfPlaneConformalMetric
        (canonicalContinuationCoverMetric x₀ g)
        (chartAt ℂ y) (chart_mem_atlas ℂ y)
        targetChart targetChart_mem_atlas y := by
    simpa [localModelOnCover, localModelOnBase] using
      PullsBackMetricInChartsAt.comp
        (F := localModelOnBase)
        (G := (canonicalContinuationCover x₀).projection)
        hprojection_chart hbase hprojection_pullback
  have heq : localModelOnCover =ᶠ[nhds y] dev := by
    filter_upwards [hUopen.mem_nhds hyU] with y' hy'
    exact (hagree y' hy').symm
  exact PullsBackMetricInChartsAt.congr_of_eventuallyEq_nhds hlocalModel heq

/--
On the canonical cover, local agreement with local-transition models gives the
actual chartwise pullback-metric identity for the continued developing map in
any source chart.

%%handwave
name: Local-transition agreement gives the metric identity in arbitrary coordinates
statement: Under local-transition model agreement, $dev$ pulls the Poincaré metric back to the canonical cover metric at every point in every compatible source and target chart.
proof: Establish the identity in the canonical source chart and transport it through a change of source chart within the complex atlas.
-/
theorem canonicalLocalTransitionAgreement_dev_pullsBackMetricInChartsAt
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev)
    (sourceChart : OpenPartialHomeomorph (canonicalContinuationCover x₀).total ℂ)
    (sourceChart_mem_atlas :
      sourceChart ∈ atlas ℂ (canonicalContinuationCover x₀).total)
    (targetChart : OpenPartialHomeomorph ℍ ℂ)
    (targetChart_mem_atlas : targetChart ∈ atlas ℂ ℍ)
    (y : (canonicalContinuationCover x₀).total) :
    PullsBackMetricInChartsAt dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g)
      sourceChart sourceChart_mem_atlas
      targetChart targetChart_mem_atlas y := by
  classical
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let localChart : HyperbolicLocalChart X g := localModels.chartAt x
  let localModelOnBase : X → ℍ := fun x' =>
    realMobiusRepresentativeAction A (localChart.toUpperHalfPlane x')
  let localModelOnCover : (canonicalContinuationCover x₀).total → ℍ := fun y' =>
    localModelOnBase ((canonicalContinuationCover x₀).projection y')
  have hy_domain :
      (canonicalContinuationCover x₀).projection y ∈ localChart.domain := by
    exact hdomain y hyU
  have hprojection_chart :
      (canonicalContinuationCover x₀).projection y ∈
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y)).source :=
    mem_chart_source ℂ ((canonicalContinuationCover x₀).projection y)
  have hbase :
      PullsBackMetricInChartsAt localModelOnBase upperHalfPlaneConformalMetric
        g.toConformalMetric
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
        (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
        targetChart targetChart_mem_atlas
        ((canonicalContinuationCover x₀).projection y) := by
    simpa [localModelOnBase, localChart] using
      hyperbolicLocalChart_realMobius_postcomp_pullsBackMetricInChartsAt_chartAt
        (X := X) localChart A hy_domain targetChart targetChart_mem_atlas
  have hprojection_pullback :
      PullsBackMetricInChartsAt
        (canonicalContinuationCover x₀).projection
        g.toConformalMetric
        (canonicalContinuationCoverMetric x₀ g)
        sourceChart sourceChart_mem_atlas
        (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
        (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
        y :=
    (canonicalContinuationCoverMetric_pullback x₀ g).in_charts_at
      sourceChart sourceChart_mem_atlas
      (chartAt ℂ ((canonicalContinuationCover x₀).projection y))
      (chart_mem_atlas ℂ ((canonicalContinuationCover x₀).projection y))
      y
  have hlocalModel :
      PullsBackMetricInChartsAt localModelOnCover upperHalfPlaneConformalMetric
        (canonicalContinuationCoverMetric x₀ g)
        sourceChart sourceChart_mem_atlas
        targetChart targetChart_mem_atlas y := by
    simpa [localModelOnCover, localModelOnBase] using
      PullsBackMetricInChartsAt.comp
        (F := localModelOnBase)
        (G := (canonicalContinuationCover x₀).projection)
        hprojection_chart hbase hprojection_pullback
  have heq : localModelOnCover =ᶠ[nhds y] dev := by
    filter_upwards [hUopen.mem_nhds hyU] with y' hy'
    exact (hagree y' hy').symm
  exact PullsBackMetricInChartsAt.congr_of_eventuallyEq_nhds hlocalModel heq

/--
%%handwave
name:
  Metric recovery for the continued developing map
statement:
  Let $\operatorname{dev}:\widetilde X_{x_0}\to\mathbb H$ locally have the
  form $A\cdot F\circ\pi$, where $A\in\mathrm{PSL}_2(\mathbb R)$ and each
  local branch $F$ satisfies $F^{*}g_{\mathbb H}=g$. Then
  $\operatorname{dev}^{*}g_{\mathbb H}=\pi^{*}g$ on
  $\widetilde X_{x_0}$.
proof:
  Work in arbitrary source and target charts and substitute the local formula
  for $\operatorname{dev}$. Real Möbius transformations preserve
  $g_{\mathbb H}$, and the local pullback identity for $F$ leaves the
  conformal factor of $\pi^{*}g$; locality then gives the global identity.
-/
theorem canonicalLocalTransitionAgreement_dev_pullsBackMetric
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev) :
    PullsBackMetric dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g) where
  in_charts := by
    intro sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas y
    exact canonicalLocalTransitionAgreement_dev_pullsBackMetricInChartsAt
      h sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas y

/--
On the canonical path-homotopy cover, local agreement with local-transition
models supplies the full developing-map regularity package.

%%handwave
name: Local-transition agreement supplies full developing-map regularity
statement: If $dev$ on the canonical cover agrees locally with local-transition hyperbolic models, then it is continuous and holomorphic, has nonzero derivative everywhere, and admits explicit local biholomorphic branches.
proof: Assemble continuity from local agreement, coordinate analyticity, derivative nonvanishing, and the local inverse branches into the regularity record.
-/
theorem canonicalLocalTransitionAgreement_dev_regular
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {dev : (canonicalContinuationCover x₀).total → ℍ}
    (h :
      HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
        (canonicalContinuationCover x₀) dev) :
    HyperbolicDevelopingMapRegularity (canonicalContinuationCover x₀) dev where
  continuous := h.continuous
  chartwise_holomorphic := canonicalLocalTransitionAgreement_dev_holomorphic h
  local_biholomorphic := canonicalLocalTransitionAgreement_dev_local_biholomorphic h
  local_biholomorphism_data :=
    canonicalLocalTransitionAgreement_dev_local_biholomorphism_data h

/--
Exact local-transition continuation fields after deriving all developing-map
regularity and metric recovery from local agreement on the canonical cover.

This is the sharper componentwise continuation boundary: analytic continuation
must construct the single-valued map, real holonomy, deck equivariance, and
local formulas.  Regularity and the pullback-metric identity are consequences
of those local formulas.
-/
structure HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- The analytically continued developing map on the canonical cover. -/
  dev : (canonicalContinuationCover x₀).total → ℍ
  /-- Lifted real holonomy obtained by monodromy of the local-transition models. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Equivariance with respect to deck transformations and lifted holonomy. -/
  equivariant :
    ∀ γ y,
      dev ((canonicalContinuationCover x₀).deckAction γ y) =
        holonomyLift.upperHalfPlaneAction γ (dev y)
  /-- The developing map locally agrees with analytic continuation of the local-transition models. -/
  agrees_with_local_models :
    HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
      (canonicalContinuationCover x₀) dev

namespace HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- Local-transition model agreement supplies continuity of the continued map.

%%handwave
name: Derived local-transition regularity includes continuity
statement: For a canonical-cover local-transition field package with derived regularity, its developing map $dev$ is continuous.
proof: Apply the continuity theorem to the package’s local-model agreement.
-/
theorem dev_continuous
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    Continuous F.dev :=
  F.agrees_with_local_models.continuous

/-- Local-transition model agreement supplies chartwise holomorphicity.

%%handwave
name: Derived local-transition regularity includes holomorphicity
statement: For such a package, $dev$ is holomorphic in the canonical cover charts.
proof: Apply holomorphicity derived from local-transition model agreement.
-/
theorem dev_holomorphic
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    HyperbolicDevelopingMapHolomorphic (canonicalContinuationCover x₀) F.dev :=
  canonicalLocalTransitionAgreement_dev_holomorphic F.agrees_with_local_models

/-- Local-transition model agreement supplies the nonzero-derivative field.

%%handwave
name: Derived local-transition regularity includes nonvanishing derivative
statement: For such a package, the coordinate derivative of $dev$ is nonzero at every canonical-cover point.
proof: Apply the nonvanishing theorem derived from local-transition model agreement.
-/
theorem dev_local_biholomorphic
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    HyperbolicDevelopingMapLocallyBiholomorphic (canonicalContinuationCover x₀) F.dev :=
  canonicalLocalTransitionAgreement_dev_local_biholomorphic F.agrees_with_local_models

/-- Local-transition model agreement supplies concrete local-biholomorphism branches.

%%handwave
name: Derived local-transition regularity includes inverse branches
statement: For such a package, every cover point has concrete local biholomorphic branch data for the coordinate expression of $dev$.
proof: Apply the local inverse-branch construction derived from local-transition agreement.
-/
theorem dev_local_biholomorphism_data
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    HyperbolicDevelopingMapLocalBiholomorphismData (canonicalContinuationCover x₀) F.dev :=
  canonicalLocalTransitionAgreement_dev_local_biholomorphism_data
    F.agrees_with_local_models

/-- Local-transition model agreement supplies the pullback metric identity.

%%handwave
name: Derived local-transition regularity includes the metric pullback
statement: For such a package, $dev^*g_{ℍ}$ equals the canonical pullback metric on the continuation cover.
proof: Apply the global metric identity derived from local-transition model agreement.
-/
theorem pullback_metric
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    PullsBackMetric F.dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g) :=
  canonicalLocalTransitionAgreement_dev_pullsBackMetric F.agrees_with_local_models

/-- Local-transition model agreement assembles the full regularity record. -/
def dev_regular
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    HyperbolicDevelopingMapRegularity (canonicalContinuationCover x₀) F.dev :=
  canonicalLocalTransitionAgreement_dev_regular F.agrees_with_local_models

/--
Reduced local-transition fields fold into the canonical-cover-metric
continuation record.
-/
def toHyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric
      x₀ g localModels where
  dev := F.dev
  dev_regular := F.dev_regular
  holonomyLift := F.holonomyLift
  pullback_metric := F.pullback_metric
  equivariant := F.equivariant
  agrees_with_local_models := F.agrees_with_local_models

/-- Reduced local-transition fields fold all the way into ordinary fields. -/
def toHyperbolicDevelopingLocalTransitionContinuationDataFields
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    HyperbolicDevelopingLocalTransitionContinuationDataFields
      x₀ g localModels :=
  F.toHyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric
    |>.toHyperbolicDevelopingLocalTransitionContinuationDataFields

/-- Forgetting derived regularity retains the original developing map.

%%handwave
name: Forgetting derived local-transition regularity preserves the developing map
statement: The underlying local-transition continuation fields have the same developing map $dev$.
proof: The forgetful construction copies the developing map.
-/
@[simp]
theorem toHyperbolicDevelopingLocalTransitionContinuationDataFields_dev
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    F.toHyperbolicDevelopingLocalTransitionContinuationDataFields.dev = F.dev :=
  rfl

/-- Forgetting derived regularity retains the canonical pullback metric.

%%handwave
name: Forgetting derived local-transition regularity preserves the cover metric
statement: The underlying local-transition fields retain the canonical pullback metric on the cover.
proof: The forgetful construction assigns the same canonical cover metric.
-/
@[simp]
theorem toHyperbolicDevelopingLocalTransitionContinuationDataFields_coverMetric
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    F.toHyperbolicDevelopingLocalTransitionContinuationDataFields.coverMetric =
      canonicalContinuationCoverMetric x₀ g :=
  rfl

end HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity

/--
PSL-valued local-transition continuation fields on the canonical cover.

This is the natural continuation endpoint for projective holonomy: analytic
continuation supplies a single-valued developing map, a real projective
holonomy representation, deck equivariance for the PSL action on `ℍ`, and
local agreement with the selected local-transition models.  Regularity and
metric recovery are derived from local agreement.
-/
structure HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- The analytically continued developing map on the canonical cover. -/
  dev : (canonicalContinuationCover x₀).total → ℍ
  /-- Real projective holonomy obtained by monodromy of the local-transition models. -/
  holonomy : RealHolonomyRepresentation X x₀
  /-- Equivariance with respect to deck transformations and PSL holonomy. -/
  equivariant :
    ∀ γ y,
      dev ((canonicalContinuationCover x₀).deckAction γ y) =
        holonomy.upperHalfPlaneAction γ (dev y)
  /-- The developing map locally agrees with analytic continuation of the local-transition models. -/
  agrees_with_local_models :
    HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
      (canonicalContinuationCover x₀) dev

namespace HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- Local-transition model agreement supplies continuity of the continued map.

%%handwave
name: Projective local-transition regularity includes continuity
statement: For a projective canonical-cover local-transition field package with derived regularity, its developing map is continuous.
proof: Apply continuity derived from the package’s local-transition model agreement.
-/
theorem dev_continuous
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
        x₀ g localModels) :
    Continuous F.dev :=
  F.agrees_with_local_models.continuous

/-- Local-transition model agreement supplies chartwise holomorphicity.

%%handwave
name: Projective local-transition regularity includes holomorphicity
statement: For such a projective package, the developing map is holomorphic in canonical-cover charts.
proof: Apply holomorphicity derived from local-transition model agreement; the projective transition formulation does not change the local branch formulas.
-/
theorem dev_holomorphic
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
        x₀ g localModels) :
    HyperbolicDevelopingMapHolomorphic (canonicalContinuationCover x₀) F.dev :=
  canonicalLocalTransitionAgreement_dev_holomorphic F.agrees_with_local_models

/-- Local-transition model agreement supplies the nonzero-derivative field.

%%handwave
name: Projective local-transition regularity includes nonvanishing derivative
statement: For such a projective package, the developing-map coordinate derivative is nonzero at every cover point.
proof: Apply the local nonvanishing theorem to the stored model agreement.
-/
theorem dev_local_biholomorphic
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
        x₀ g localModels) :
    HyperbolicDevelopingMapLocallyBiholomorphic (canonicalContinuationCover x₀) F.dev :=
  canonicalLocalTransitionAgreement_dev_local_biholomorphic F.agrees_with_local_models

/-- Local-transition model agreement supplies concrete local-biholomorphism branches.

%%handwave
name: Projective local-transition regularity includes local inverse branches
statement: For such a projective package, every point admits concrete local biholomorphic branch data for the developing-map coordinate expression.
proof: Use analyticity and nonzero derivative derived from local-transition agreement, then apply the local inverse-function branch theorem.
-/
theorem dev_local_biholomorphism_data
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
        x₀ g localModels) :
    HyperbolicDevelopingMapLocalBiholomorphismData (canonicalContinuationCover x₀) F.dev :=
  canonicalLocalTransitionAgreement_dev_local_biholomorphism_data
    F.agrees_with_local_models

/-- Local-transition model agreement supplies the pullback metric identity.

%%handwave
name: Projective local-transition regularity includes the metric pullback
statement: For such a projective package, $dev^*g_{ℍ}$ is the canonical cover metric.
proof: Apply the metric identity derived from the package’s local model agreement.
-/
theorem pullback_metric
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
        x₀ g localModels) :
    PullsBackMetric F.dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g) :=
  canonicalLocalTransitionAgreement_dev_pullsBackMetric F.agrees_with_local_models

/-- Local-transition model agreement assembles the full regularity record. -/
def dev_regular
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
        x₀ g localModels) :
    HyperbolicDevelopingMapRegularity (canonicalContinuationCover x₀) F.dev :=
  canonicalLocalTransitionAgreement_dev_regular F.agrees_with_local_models

/-- PSL-valued reduced fields fold directly into the ordinary developing-map record. -/
def toHyperbolicDevelopingMap
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
        x₀ g localModels) :
    HyperbolicDevelopingMap X x₀ g where
  cover := canonicalContinuationCover x₀
  dev := F.dev
  coverMetric := canonicalContinuationCoverMetric x₀ g
  coverMetric_pullback := canonicalContinuationCoverMetric_pullback x₀ g
  dev_regular := F.dev_regular
  holonomy := F.holonomy
  pullback_metric := F.pullback_metric
  equivariant := F.equivariant

/-- A lifted reduced continuation field forgets to the PSL-valued reduced field. -/
def ofLifted
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
      x₀ g localModels where
  dev := F.dev
  holonomy := F.holonomyLift.toRealHolonomyRepresentation
  equivariant := by
    intro γ y
    trans F.holonomyLift.upperHalfPlaneAction γ (F.dev y)
    · exact F.equivariant γ y
    · symm
      exact (F.holonomyLift.toRealHolonomyRepresentation_isInducedByLift).2 γ (F.dev y)
  agrees_with_local_models := F.agrees_with_local_models

/-- The projective derived-regularity package built from lifted data retains the lifted developing map.

%%handwave
name: Projectivizing lifted regularity preserves the developing map
statement: When a lifted regularity package is converted to its projective form, the developing map remains exactly $dev$.
proof: The conversion copies the developing-map field.
-/
@[simp]
theorem ofLifted_dev
    (F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    (ofLifted F).dev = F.dev :=
  rfl

end HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL

/--
Exact remaining fields after also deriving continuity from local-model agreement.

Compared with
`HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetric`, this record
does not ask for the continuity component of `dev_regular` or the pullback
metric identity: both are proved from `agrees_with_local_models`.  The
holomorphic, local-biholomorphic, holonomy, equivariance, and local agreement
obligations remain the original ones.
-/
structure HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedContinuity
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- The analytically continued developing map on the canonical cover. -/
  dev : (canonicalContinuationCover x₀).total → ℍ
  /-- The developing map is holomorphic in local complex coordinates. -/
  dev_holomorphic :
    HyperbolicDevelopingMapHolomorphic (canonicalContinuationCover x₀) dev
  /-- The local complex-coordinate expression has nonzero derivative. -/
  dev_local_biholomorphic :
    HyperbolicDevelopingMapLocallyBiholomorphic (canonicalContinuationCover x₀) dev
  /-- The local complex-coordinate expression is represented by local homeomorphism branches. -/
  dev_local_biholomorphism_data :
    HyperbolicDevelopingMapLocalBiholomorphismData (canonicalContinuationCover x₀) dev
  /-- Lifted real holonomy obtained by monodromy of the local models. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Equivariance with respect to deck transformations and lifted holonomy. -/
  equivariant :
    ∀ γ y,
      dev ((canonicalContinuationCover x₀).deckAction γ y) =
        holonomyLift.upperHalfPlaneAction γ (dev y)
  /-- The developing map locally agrees with analytic continuation of the local models. -/
  agrees_with_local_models :
    HyperbolicDevelopingAgreesWithLocalModels localModels
      (canonicalContinuationCover x₀) dev

namespace HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedContinuity

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- Local-model agreement supplies the continuity part of developing-map regularity.

%%handwave
name: Derived continuity gives a continuous developing map
statement: For canonical-cover global-model fields with continuity derived from local agreement, the developing map is continuous.
proof: Apply continuity from the stored local model agreement.
-/
theorem dev_continuous
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedContinuity
        x₀ g localModels) :
    Continuous F.dev :=
  F.agrees_with_local_models.continuous

/-- Local-model agreement supplies the pullback metric identity.

%%handwave
name: Derived continuity fields retain the metric pullback identity
statement: For these canonical-cover fields, $dev^*g_{ℍ}$ equals the canonical cover metric.
proof: The metric pullback is already part of the underlying continuation fields and is retained by the derived-continuity package.
-/
theorem pullback_metric
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedContinuity
        x₀ g localModels) :
    PullsBackMetric F.dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g) :=
  canonicalAgreement_dev_pullsBackMetric F.agrees_with_local_models

/-- The reduced regularity fields assemble into the original regularity record. -/
def dev_regular
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedContinuity
        x₀ g localModels) :
    HyperbolicDevelopingMapRegularity (canonicalContinuationCover x₀) F.dev where
  continuous := F.dev_continuous
  chartwise_holomorphic := F.dev_holomorphic
  local_biholomorphic := F.dev_local_biholomorphic
  local_biholomorphism_data := F.dev_local_biholomorphism_data

/--
Fields remaining after deriving continuity fold into the canonical-cover-metric
continuation record.
-/
def toHyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetric
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedContinuity
        x₀ g localModels) :
    HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetric x₀ g localModels where
  dev := F.dev
  dev_regular := F.dev_regular
  holonomyLift := F.holonomyLift
  pullback_metric := F.pullback_metric
  equivariant := F.equivariant
  agrees_with_local_models := F.agrees_with_local_models

/-- The reduced fields fold all the way back into the original continuation-fields target. -/
def toHyperbolicDevelopingContinuationDataFields
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedContinuity
        x₀ g localModels) :
    HyperbolicDevelopingContinuationDataFields x₀ g localModels :=
  F.toHyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetric
    |>.toHyperbolicDevelopingContinuationDataFields

/-- Forgetting derived continuity retains the developing map.

%%handwave
name: Forgetting derived continuity preserves the developing map
statement: The underlying continuation fields have the same developing map.
proof: The forgetful construction copies $dev$.
-/
@[simp]
theorem toHyperbolicDevelopingContinuationDataFields_dev
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedContinuity
        x₀ g localModels) :
    F.toHyperbolicDevelopingContinuationDataFields.dev = F.dev :=
  rfl

/-- Forgetting derived continuity retains the canonical cover metric.

%%handwave
name: Forgetting derived continuity preserves the canonical metric
statement: The underlying continuation fields retain the canonical pullback metric on the path-homotopy cover.
proof: The forgetful construction copies the cover metric.
-/
@[simp]
theorem toHyperbolicDevelopingContinuationDataFields_coverMetric
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedContinuity
        x₀ g localModels) :
    F.toHyperbolicDevelopingContinuationDataFields.coverMetric =
      canonicalContinuationCoverMetric x₀ g :=
  rfl

end HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedContinuity

/--
Exact remaining fields after deriving both continuity and chartwise
holomorphicity from local-model agreement on the canonical cover.

The remaining regularity inputs are precisely the local-biholomorphism
nonvanishing derivative and the concrete local-homeomorphism branch data.
-/
structure HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedHolomorphic
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- The analytically continued developing map on the canonical cover. -/
  dev : (canonicalContinuationCover x₀).total → ℍ
  /-- The local complex-coordinate expression has nonzero derivative. -/
  dev_local_biholomorphic :
    HyperbolicDevelopingMapLocallyBiholomorphic (canonicalContinuationCover x₀) dev
  /-- The local complex-coordinate expression is represented by local homeomorphism branches. -/
  dev_local_biholomorphism_data :
    HyperbolicDevelopingMapLocalBiholomorphismData (canonicalContinuationCover x₀) dev
  /-- Lifted real holonomy obtained by monodromy of the local models. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Equivariance with respect to deck transformations and lifted holonomy. -/
  equivariant :
    ∀ γ y,
      dev ((canonicalContinuationCover x₀).deckAction γ y) =
        holonomyLift.upperHalfPlaneAction γ (dev y)
  /-- The developing map locally agrees with analytic continuation of the local models. -/
  agrees_with_local_models :
    HyperbolicDevelopingAgreesWithLocalModels localModels
      (canonicalContinuationCover x₀) dev

namespace HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedHolomorphic

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- Local-model agreement supplies continuity of the continued map.

%%handwave
name: Derived holomorphic fields include continuity
statement: For canonical-cover continuation fields with holomorphicity derived from local agreement, the developing map is continuous.
proof: Apply continuity from the stored local-model agreement.
-/
theorem dev_continuous
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedHolomorphic
        x₀ g localModels) :
    Continuous F.dev :=
  F.agrees_with_local_models.continuous

/-- Local-model agreement supplies chartwise holomorphicity on the canonical cover.

%%handwave
name: Derived holomorphic fields have a holomorphic developing map
statement: For these fields, $dev$ is holomorphic in canonical-cover charts.
proof: Apply the canonical-cover holomorphicity theorem to the stored local-model agreement.
-/
theorem dev_holomorphic
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedHolomorphic
        x₀ g localModels) :
    HyperbolicDevelopingMapHolomorphic (canonicalContinuationCover x₀) F.dev :=
  canonicalAgreement_dev_holomorphic F.agrees_with_local_models

/-- Local-model agreement supplies the pullback metric identity.

%%handwave
name: Derived holomorphic fields retain the metric identity
statement: For these fields, $dev^*g_{ℍ}$ equals the canonical pullback metric.
proof: The underlying continuation fields already carry this pullback identity.
-/
theorem pullback_metric
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedHolomorphic
        x₀ g localModels) :
    PullsBackMetric F.dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g) :=
  canonicalAgreement_dev_pullsBackMetric F.agrees_with_local_models

/-- Derived continuity and holomorphicity assemble with the remaining regularity fields. -/
def dev_regular
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedHolomorphic
        x₀ g localModels) :
    HyperbolicDevelopingMapRegularity (canonicalContinuationCover x₀) F.dev where
  continuous := F.dev_continuous
  chartwise_holomorphic := F.dev_holomorphic
  local_biholomorphic := F.dev_local_biholomorphic
  local_biholomorphism_data := F.dev_local_biholomorphism_data

/--
Fields remaining after deriving holomorphicity fold into the previous reduced
continuation record.
-/
def toHyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedContinuity
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedHolomorphic
        x₀ g localModels) :
    HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedContinuity
      x₀ g localModels where
  dev := F.dev
  dev_holomorphic := F.dev_holomorphic
  dev_local_biholomorphic := F.dev_local_biholomorphic
  dev_local_biholomorphism_data := F.dev_local_biholomorphism_data
  holonomyLift := F.holonomyLift
  equivariant := F.equivariant
  agrees_with_local_models := F.agrees_with_local_models

/-- The reduced fields fold all the way back into the original continuation-fields target. -/
def toHyperbolicDevelopingContinuationDataFields
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedHolomorphic
        x₀ g localModels) :
    HyperbolicDevelopingContinuationDataFields x₀ g localModels :=
  F.toHyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedContinuity
    |>.toHyperbolicDevelopingContinuationDataFields

/-- Forgetting derived holomorphicity retains the developing map.

%%handwave
name: Forgetting derived holomorphicity preserves the developing map
statement: The underlying continuation field package has the same developing map.
proof: The forgetful construction copies $dev$.
-/
@[simp]
theorem toHyperbolicDevelopingContinuationDataFields_dev
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedHolomorphic
        x₀ g localModels) :
    F.toHyperbolicDevelopingContinuationDataFields.dev = F.dev :=
  rfl

/-- Forgetting derived holomorphicity retains the canonical cover metric.

%%handwave
name: Forgetting derived holomorphicity preserves the canonical metric
statement: The underlying fields retain the canonical cover metric.
proof: The forgetful construction copies the metric field.
-/
@[simp]
theorem toHyperbolicDevelopingContinuationDataFields_coverMetric
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedHolomorphic
        x₀ g localModels) :
    F.toHyperbolicDevelopingContinuationDataFields.coverMetric =
      canonicalContinuationCoverMetric x₀ g :=
  rfl

end HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedHolomorphic

/--
Exact remaining fields after deriving continuity, chartwise holomorphicity, and
the nonzero-derivative local-biholomorphism condition from local-model
agreement on the canonical cover.

The only remaining regularity field is the concrete local-homeomorphism branch
data used downstream by projectivization.
-/
structure HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- The analytically continued developing map on the canonical cover. -/
  dev : (canonicalContinuationCover x₀).total → ℍ
  /-- The local complex-coordinate expression is represented by local homeomorphism branches. -/
  dev_local_biholomorphism_data :
    HyperbolicDevelopingMapLocalBiholomorphismData (canonicalContinuationCover x₀) dev
  /-- Lifted real holonomy obtained by monodromy of the local models. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Equivariance with respect to deck transformations and lifted holonomy. -/
  equivariant :
    ∀ γ y,
      dev ((canonicalContinuationCover x₀).deckAction γ y) =
        holonomyLift.upperHalfPlaneAction γ (dev y)
  /-- The developing map locally agrees with analytic continuation of the local models. -/
  agrees_with_local_models :
    HyperbolicDevelopingAgreesWithLocalModels localModels
      (canonicalContinuationCover x₀) dev

namespace HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- Local-model agreement supplies continuity of the continued map.

%%handwave
name: Derived local biholomorphic fields include continuity
statement: For canonical-cover fields with local biholomorphicity derived from model agreement, the developing map is continuous.
proof: Apply continuity from local-model agreement.
-/
theorem dev_continuous
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic
        x₀ g localModels) :
    Continuous F.dev :=
  F.agrees_with_local_models.continuous

/-- Local-model agreement supplies chartwise holomorphicity on the canonical cover.

%%handwave
name: Derived local biholomorphic fields include holomorphicity
statement: For these fields, $dev$ is holomorphic in canonical-cover charts.
proof: Apply holomorphicity from local-model agreement.
-/
theorem dev_holomorphic
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic
        x₀ g localModels) :
    HyperbolicDevelopingMapHolomorphic (canonicalContinuationCover x₀) F.dev :=
  canonicalAgreement_dev_holomorphic F.agrees_with_local_models

/-- Local-model agreement supplies the nonzero-derivative local-biholomorphism field.

%%handwave
name: Derived local biholomorphic fields have nonzero derivative
statement: For these fields, the developing-map coordinate derivative is nonzero at every cover point.
proof: Apply derivative nonvanishing derived from local-model agreement.
-/
theorem dev_local_biholomorphic
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic
        x₀ g localModels) :
    HyperbolicDevelopingMapLocallyBiholomorphic (canonicalContinuationCover x₀) F.dev :=
  canonicalAgreement_dev_local_biholomorphic F.agrees_with_local_models

/-- Local-model agreement supplies the pullback metric identity.

%%handwave
name: Derived local biholomorphic fields retain the metric identity
statement: For these fields, $dev^*g_{ℍ}$ equals the canonical cover metric.
proof: Use the pullback identity stored in the underlying fields.
-/
theorem pullback_metric
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic
        x₀ g localModels) :
    PullsBackMetric F.dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g) :=
  canonicalAgreement_dev_pullsBackMetric F.agrees_with_local_models

/-- Derived local regularity assembles with the remaining branch-data field. -/
def dev_regular
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic
        x₀ g localModels) :
    HyperbolicDevelopingMapRegularity (canonicalContinuationCover x₀) F.dev where
  continuous := F.dev_continuous
  chartwise_holomorphic := F.dev_holomorphic
  local_biholomorphic := F.dev_local_biholomorphic
  local_biholomorphism_data := F.dev_local_biholomorphism_data

/--
Fields remaining after deriving local biholomorphicity fold into the previous
reduced continuation record.
-/
def toHyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedHolomorphic
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic
        x₀ g localModels) :
    HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedHolomorphic
      x₀ g localModels where
  dev := F.dev
  dev_local_biholomorphic := F.dev_local_biholomorphic
  dev_local_biholomorphism_data := F.dev_local_biholomorphism_data
  holonomyLift := F.holonomyLift
  equivariant := F.equivariant
  agrees_with_local_models := F.agrees_with_local_models

/-- The reduced fields fold all the way back into the original continuation-fields target. -/
def toHyperbolicDevelopingContinuationDataFields
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic
        x₀ g localModels) :
    HyperbolicDevelopingContinuationDataFields x₀ g localModels :=
  F.toHyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedHolomorphic
    |>.toHyperbolicDevelopingContinuationDataFields

/-- Forgetting derived local biholomorphicity retains the developing map.

%%handwave
name: Forgetting derived local biholomorphicity preserves the developing map
statement: The underlying continuation fields have the same map $dev$.
proof: The forgetful construction copies the developing map.
-/
@[simp]
theorem toHyperbolicDevelopingContinuationDataFields_dev
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic
        x₀ g localModels) :
    F.toHyperbolicDevelopingContinuationDataFields.dev = F.dev :=
  rfl

/-- Forgetting derived local biholomorphicity retains the canonical cover metric.

%%handwave
name: Forgetting derived local biholomorphicity preserves the canonical metric
statement: The underlying continuation fields retain the canonical cover metric.
proof: The forgetful construction copies the metric.
-/
@[simp]
theorem toHyperbolicDevelopingContinuationDataFields_coverMetric
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic
        x₀ g localModels) :
    F.toHyperbolicDevelopingContinuationDataFields.coverMetric =
      canonicalContinuationCoverMetric x₀ g :=
  rfl

end HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic

/--
Exact remaining fields after deriving all developing-map regularity from
local-model agreement on the canonical cover.

At this stage the continuation boundary has no separate regularity
obligations: continuity, chartwise holomorphicity, nonzero derivative, and the
concrete local-homeomorphism branch data are all consequences of the local
agreement field.
-/
structure HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- The analytically continued developing map on the canonical cover. -/
  dev : (canonicalContinuationCover x₀).total → ℍ
  /-- Lifted real holonomy obtained by monodromy of the local models. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Equivariance with respect to deck transformations and lifted holonomy. -/
  equivariant :
    ∀ γ y,
      dev ((canonicalContinuationCover x₀).deckAction γ y) =
        holonomyLift.upperHalfPlaneAction γ (dev y)
  /-- The developing map locally agrees with analytic continuation of the local models. -/
  agrees_with_local_models :
    HyperbolicDevelopingAgreesWithLocalModels localModels
      (canonicalContinuationCover x₀) dev

namespace HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- Local-model agreement supplies continuity of the continued map.

%%handwave
name: Full derived regularity includes continuity
statement: For a canonical-cover field package with full regularity derived from local-model agreement, the developing map is continuous.
proof: Apply continuity from the stored local agreement.
-/
theorem dev_continuous
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    Continuous F.dev :=
  F.agrees_with_local_models.continuous

/-- Local-model agreement supplies chartwise holomorphicity on the canonical cover.

%%handwave
name: Full derived regularity includes holomorphicity
statement: For a canonical-cover field package with full regularity derived from model agreement, $dev$ is holomorphic.
proof: Apply the canonical-cover holomorphicity theorem to the stored local agreement.
-/
theorem dev_holomorphic
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    HyperbolicDevelopingMapHolomorphic (canonicalContinuationCover x₀) F.dev :=
  canonicalAgreement_dev_holomorphic F.agrees_with_local_models

/-- Local-model agreement supplies the nonzero-derivative local-biholomorphism field.

%%handwave
name: Full derived regularity includes nonvanishing derivative
statement: For such a package, the developing-map coordinate derivative is nonzero at every cover point.
proof: Apply derivative nonvanishing derived from local-model agreement.
-/
theorem dev_local_biholomorphic
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    HyperbolicDevelopingMapLocallyBiholomorphic (canonicalContinuationCover x₀) F.dev :=
  canonicalAgreement_dev_local_biholomorphic F.agrees_with_local_models

/-- Local-model agreement supplies the concrete local-homeomorphism branch data.

%%handwave
name: Full derived regularity includes local inverse branches
statement: For such a package, every cover point admits concrete local biholomorphic branch data for $dev$.
proof: Apply the analytic inverse-branch construction derived from local agreement.
-/
theorem dev_local_biholomorphism_data
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    HyperbolicDevelopingMapLocalBiholomorphismData (canonicalContinuationCover x₀) F.dev :=
  canonicalAgreement_dev_local_biholomorphism_data F.agrees_with_local_models

/-- Local-model agreement supplies the pullback metric identity.

%%handwave
name: Full derived regularity includes the metric pullback
statement: For such a package, $dev^*g_{ℍ}$ equals the canonical pullback metric.
proof: Apply the metric identity supplied by local-model agreement.
-/
theorem pullback_metric
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    PullsBackMetric F.dev upperHalfPlaneConformalMetric
      (canonicalContinuationCoverMetric x₀ g) :=
  canonicalAgreement_dev_pullsBackMetric F.agrees_with_local_models

/-- Local-model agreement assembles the full developing-map regularity record. -/
def dev_regular
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    HyperbolicDevelopingMapRegularity (canonicalContinuationCover x₀) F.dev :=
  canonicalAgreement_dev_regular F.agrees_with_local_models

/--
Fields remaining after deriving all regularity fold into the previous reduced
continuation record.
-/
def toHyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic
      x₀ g localModels where
  dev := F.dev
  dev_local_biholomorphism_data := F.dev_local_biholomorphism_data
  holonomyLift := F.holonomyLift
  equivariant := F.equivariant
  agrees_with_local_models := F.agrees_with_local_models

/-- The reduced fields fold all the way back into the original continuation-fields target. -/
def toHyperbolicDevelopingContinuationDataFields
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    HyperbolicDevelopingContinuationDataFields x₀ g localModels :=
  F.toHyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedLocalBiholomorphic
    |>.toHyperbolicDevelopingContinuationDataFields

/-- Forgetting the full derived regularity package retains the developing map.

%%handwave
name: Forgetting full derived regularity preserves the developing map
statement: The underlying continuation fields have exactly the same map $dev$.
proof: The forgetful construction copies the developing map.
-/
@[simp]
theorem toHyperbolicDevelopingContinuationDataFields_dev
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    F.toHyperbolicDevelopingContinuationDataFields.dev = F.dev :=
  rfl

/-- Forgetting the full derived regularity package retains the canonical cover metric.

%%handwave
name: Forgetting full derived regularity preserves the canonical metric
statement: The underlying fields retain the canonical metric on the path-homotopy cover.
proof: The forgetful construction copies the cover metric.
-/
@[simp]
theorem toHyperbolicDevelopingContinuationDataFields_coverMetric
    (F :
      HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels) :
    F.toHyperbolicDevelopingContinuationDataFields.coverMetric =
      canonicalContinuationCoverMetric x₀ g :=
  rfl

end HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity

/--
Local sheetwise continuation data on the canonical cover.

This is the concrete boundary around analytic continuation: near every point of
the canonical cover the continued map is not merely asserted to be regular, but
is explicitly one of the chosen upper-half-plane local models, postcomposed by a
real Mobius representative.
-/
structure CanonicalCoverLocalContinuationData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- The single-valued map obtained by continuing local models to the cover. -/
  dev : (canonicalContinuationCover x₀).total → ℍ
  /-- The local model used near a point of the cover. -/
  centerAt : (canonicalContinuationCover x₀).total → X
  /-- The real Mobius postcomposition relating the branch to the chosen model. -/
  mobiusAt : (canonicalContinuationCover x₀).total → RealMobiusRepresentative
  /-- A cover-neighborhood on which the displayed branch formula is valid. -/
  neighborhoodAt :
    (canonicalContinuationCover x₀).total →
      Set (canonicalContinuationCover x₀).total
  /-- The branch formula holds on an open neighborhood. -/
  isOpen_neighborhoodAt :
    ∀ y, IsOpen (neighborhoodAt y)
  /-- The neighborhood is centered at the requested point. -/
  mem_neighborhoodAt :
    ∀ y, y ∈ neighborhoodAt y
  /-- Points in the sheet project into the domain of the selected local model. -/
  projection_mem_model_domain :
    ∀ y y', y' ∈ neighborhoodAt y →
      (canonicalContinuationCover x₀).projection y' ∈
        (localModels.chartAt (centerAt y)).domain
  /-- On each sheet, the continued map is the selected model up to real Mobius action. -/
  dev_eq_on_neighborhood :
    ∀ y y', y' ∈ neighborhoodAt y →
      dev y' =
        realMobiusRepresentativeAction (mobiusAt y)
          ((localModels.chartAt (centerAt y)).toUpperHalfPlane
            ((canonicalContinuationCover x₀).projection y'))

namespace CanonicalCoverLocalContinuationData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/--
The sheetwise continuation boundary supplies the local-model agreement
predicate consumed by the regularity and metric-pullback derivations.
-/
def agreesWithLocalModels
    (C : CanonicalCoverLocalContinuationData x₀ g localModels) :
    HyperbolicDevelopingAgreesWithLocalModels localModels
      (canonicalContinuationCover x₀) C.dev := by
  intro y
  refine ⟨C.neighborhoodAt y, C.isOpen_neighborhoodAt y,
    C.mem_neighborhoodAt y, C.centerAt y, C.mobiusAt y, ?_, ?_⟩
  · exact C.projection_mem_model_domain y
  · exact C.dev_eq_on_neighborhood y

end CanonicalCoverLocalContinuationData

/--
Monodromy data for analytic continuation of the chosen local models.

The local-continuation field records the actual sheetwise analytic branches on
the canonical cover.  The holonomy and equivariance fields record the real
Mobius monodromy obtained when those branches are transported by deck
transformations.
-/
structure AnalyticContinuationMonodromyData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- Explicit local branch formulas for the continued developing map. -/
  localContinuation :
    CanonicalCoverLocalContinuationData x₀ g localModels
  /-- Lifted real holonomy produced by monodromy of the local models. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Deck transformations act on the continued branches by real Mobius holonomy. -/
  equivariant :
    ∀ γ y,
      localContinuation.dev ((canonicalContinuationCover x₀).deckAction γ y) =
        holonomyLift.upperHalfPlaneAction γ (localContinuation.dev y)

namespace AnalyticContinuationMonodromyData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- The continued developing map carried by monodromy data. -/
def dev (M : AnalyticContinuationMonodromyData x₀ g localModels) :
    (canonicalContinuationCover x₀).total → ℍ :=
  M.localContinuation.dev

/-- Monodromy data imply the reduced continuation fields. -/
def toDerivedRegularityFields
    (M : AnalyticContinuationMonodromyData x₀ g localModels) :
    HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
      x₀ g localModels where
  dev := M.dev
  holonomyLift := M.holonomyLift
  equivariant := M.equivariant
  agrees_with_local_models := M.localContinuation.agreesWithLocalModels

/-- The regularity fields derived from analytic-continuation monodromy retain its developing map.

%%handwave
name: Regularity derived from analytic monodromy preserves the developing map
statement: If regularity fields are constructed from analytic-continuation monodromy data $M$, their developing map equals the original map of $M$.
proof: The construction passes the original developing map through the intermediate continuation field packages unchanged.
-/
@[simp]
theorem toDerivedRegularityFields_dev
    (M : AnalyticContinuationMonodromyData x₀ g localModels) :
    M.toDerivedRegularityFields.dev = M.dev :=
  rfl

end AnalyticContinuationMonodromyData

/--
Local sheetwise continuation data on the canonical cover for a
local-transition atlas.

This is the componentwise-overlap analogue of
`CanonicalCoverLocalContinuationData`: every sheet is explicitly one selected
upper-half-plane local model, postcomposed by a real Mobius representative.
-/
structure CanonicalCoverLocalTransitionContinuationData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- The single-valued map obtained by continuing local models to the cover. -/
  dev : (canonicalContinuationCover x₀).total → ℍ
  /-- The local model used near a point of the cover. -/
  centerAt : (canonicalContinuationCover x₀).total → X
  /-- The real Mobius postcomposition relating the branch to the chosen model. -/
  mobiusAt : (canonicalContinuationCover x₀).total → RealMobiusRepresentative
  /-- A cover-neighborhood on which the displayed branch formula is valid. -/
  neighborhoodAt :
    (canonicalContinuationCover x₀).total →
      Set (canonicalContinuationCover x₀).total
  /-- The branch formula holds on an open neighborhood. -/
  isOpen_neighborhoodAt :
    ∀ y, IsOpen (neighborhoodAt y)
  /-- The neighborhood is centered at the requested point. -/
  mem_neighborhoodAt :
    ∀ y, y ∈ neighborhoodAt y
  /-- Points in the sheet project into the domain of the selected local model. -/
  projection_mem_model_domain :
    ∀ y y', y' ∈ neighborhoodAt y →
      (canonicalContinuationCover x₀).projection y' ∈
        (localModels.chartAt (centerAt y)).domain
  /-- On each sheet, the continued map is the selected model up to real Mobius action. -/
  dev_eq_on_neighborhood :
    ∀ y y', y' ∈ neighborhoodAt y →
      dev y' =
        realMobiusRepresentativeAction (mobiusAt y)
          ((localModels.chartAt (centerAt y)).toUpperHalfPlane
            ((canonicalContinuationCover x₀).projection y'))

namespace CanonicalCoverLocalTransitionContinuationData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
The sheetwise local-transition continuation boundary supplies the local
agreement predicate consumed by the regularity and metric-pullback derivations.
-/
def agreesWithLocalTransitionModels
    (C : CanonicalCoverLocalTransitionContinuationData x₀ g localModels) :
    HyperbolicDevelopingAgreesWithLocalTransitionModels localModels
      (canonicalContinuationCover x₀) C.dev := by
  intro y
  refine ⟨C.neighborhoodAt y, C.isOpen_neighborhoodAt y,
    C.mem_neighborhoodAt y, C.centerAt y, C.mobiusAt y, ?_, ?_⟩
  · exact C.projection_mem_model_domain y
  · exact C.dev_eq_on_neighborhood y

end CanonicalCoverLocalTransitionContinuationData

/--
Monodromy data for analytic continuation of a local-transition atlas.

The local-continuation field records the actual sheetwise analytic branches on
the canonical cover.  The holonomy and equivariance fields record the real
Mobius monodromy obtained when those branches are transported by deck
transformations.
-/
structure LocalTransitionAnalyticContinuationMonodromyData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Explicit local branch formulas for the continued developing map. -/
  localContinuation :
    CanonicalCoverLocalTransitionContinuationData x₀ g localModels
  /-- Lifted real holonomy produced by monodromy of the local-transition models. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Deck transformations act on the continued branches by real Mobius holonomy. -/
  equivariant :
    ∀ γ y,
      localContinuation.dev ((canonicalContinuationCover x₀).deckAction γ y) =
        holonomyLift.upperHalfPlaneAction γ (localContinuation.dev y)

namespace LocalTransitionAnalyticContinuationMonodromyData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- The continued developing map carried by local-transition monodromy data. -/
def dev (M : LocalTransitionAnalyticContinuationMonodromyData x₀ g localModels) :
    (canonicalContinuationCover x₀).total → ℍ :=
  M.localContinuation.dev

/-- Local-transition monodromy data imply the reduced continuation fields. -/
def toDerivedRegularityFields
    (M : LocalTransitionAnalyticContinuationMonodromyData x₀ g localModels) :
    HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
      x₀ g localModels where
  dev := M.dev
  holonomyLift := M.holonomyLift
  equivariant := M.equivariant
  agrees_with_local_models :=
    M.localContinuation.agreesWithLocalTransitionModels

/-- The regularity fields derived from local-transition monodromy retain its developing map.

%%handwave
name: Regularity derived from local-transition monodromy preserves the developing map
statement: If regularity fields are constructed from local-transition analytic monodromy data $M$, their developing map equals the original map of $M$.
proof: The construction copies the developing map while deriving continuity, holomorphicity, local inverse branches, and the metric identity.
-/
@[simp]
theorem toDerivedRegularityFields_dev
    (M : LocalTransitionAnalyticContinuationMonodromyData x₀ g localModels) :
    M.toDerivedRegularityFields.dev = M.dev :=
  rfl

end LocalTransitionAnalyticContinuationMonodromyData

/--
Analytic continuation indexed by endpoint and path-homotopy class for a
local-transition atlas.

This is the componentwise-overlap analogue of
`PathClassAnalyticContinuationData`.  The stored local sheet formula only asks
for a selected local model and a real Mobius postcomposition near each point
of the path-homotopy cover; regularity and metric recovery are derived later
from these formulas.
-/
structure PathClassLocalTransitionAnalyticContinuationData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- The continued value associated to an endpoint and path-homotopy class. -/
  valueAt : ∀ x : X, Path.Homotopic.Quotient x₀ x → ℍ
  /-- The selected local model controlling the branch near this path class. -/
  centerAt : ∀ x : X, Path.Homotopic.Quotient x₀ x → X
  /-- The real Mobius postcomposition relating the branch to the selected model. -/
  mobiusAt :
    ∀ x : X, Path.Homotopic.Quotient x₀ x → RealMobiusRepresentative
  /--
  A neighborhood of the corresponding path-homotopy-cover point on which the
  branch formula is valid.
  -/
  neighborhoodAt :
    ∀ x : X, Path.Homotopic.Quotient x₀ x →
      Set (PathHomotopyUniversalCover X x₀)
  /-- The branch neighborhood is open in the path-homotopy cover. -/
  isOpen_neighborhoodAt :
    ∀ x q, IsOpen (neighborhoodAt x q)
  /-- The branch neighborhood contains the path-class point it describes. -/
  mem_neighborhoodAt :
    ∀ x q, (⟨x, q⟩ : PathHomotopyUniversalCover X x₀) ∈ neighborhoodAt x q
  /-- Points in the branch neighborhood project into the selected model domain. -/
  endpoint_mem_model_domain :
    ∀ x q y', y' ∈ neighborhoodAt x q →
      PathHomotopyUniversalCover.endpoint y' ∈
        (localModels.chartAt (centerAt x q)).domain
  /--
  On the branch neighborhood, path-class values are the selected local model up
  to real Mobius action.
  -/
  value_eq_on_neighborhood :
    ∀ x q y', y' ∈ neighborhoodAt x q →
      valueAt (PathHomotopyUniversalCover.endpoint y')
          (PathHomotopyUniversalCover.pathClass y') =
        realMobiusRepresentativeAction (mobiusAt x q)
          ((localModels.chartAt (centerAt x q)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y'))

namespace PathClassLocalTransitionAnalyticContinuationData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- The cover-level developing map determined by path-class continuation data. -/
def dev
    (C :
      PathClassLocalTransitionAnalyticContinuationData x₀ g localModels) :
    (canonicalContinuationCover x₀).total → ℍ :=
  fun y =>
    C.valueAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)

/--
Path-class local-transition continuation data fold into the sheetwise
continuation data on the canonical cover.
-/
def toCanonicalCoverLocalTransitionContinuationData
    (C :
      PathClassLocalTransitionAnalyticContinuationData x₀ g localModels) :
    CanonicalCoverLocalTransitionContinuationData x₀ g localModels where
  dev := C.dev
  centerAt := fun y =>
    C.centerAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)
  mobiusAt := fun y =>
    C.mobiusAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)
  neighborhoodAt := fun y =>
    C.neighborhoodAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)
  isOpen_neighborhoodAt := by
    intro y
    exact C.isOpen_neighborhoodAt
      (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)
  mem_neighborhoodAt := by
    intro y
    exact C.mem_neighborhoodAt
      (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)
  projection_mem_model_domain := by
    intro y y' hy'
    simpa [canonicalContinuationCover] using
      C.endpoint_mem_model_domain
        (PathHomotopyUniversalCover.endpoint y)
        (PathHomotopyUniversalCover.pathClass y) y' hy'
  dev_eq_on_neighborhood := by
    intro y y' hy'
    simpa [dev, canonicalContinuationCover] using
      C.value_eq_on_neighborhood
        (PathHomotopyUniversalCover.endpoint y)
        (PathHomotopyUniversalCover.pathClass y) y' hy'

/-- Lifting path-class continuation data to the canonical cover preserves the developing map.

%%handwave
name: Canonical lifting preserves the path-class developing map
statement: For path-class local-transition continuation data $C$, the developing map of its lift to the canonical cover equals the original path-class map: $dev_{lift}=dev_C$.
proof: The lifted package defines its map by evaluating the original data at the endpoint and path class of each cover point, which is exactly the original developing map.
-/
@[simp]
theorem toCanonicalCoverLocalTransitionContinuationData_dev
    (C :
      PathClassLocalTransitionAnalyticContinuationData x₀ g localModels) :
    C.toCanonicalCoverLocalTransitionContinuationData.dev = C.dev :=
  rfl

/-- Lifting path-class continuation data preserves the selected local-chart center.

%%handwave
name: Canonical lifting preserves the selected chart center
statement: For a canonical-cover point $y$, the lifted chart center is $c(π(y),[y])$, the center assigned by the path-class data to its endpoint and path class.
proof: This is the definition of the lifted center field.
-/
@[simp]
theorem toCanonicalCoverLocalTransitionContinuationData_centerAt
    (C :
      PathClassLocalTransitionAnalyticContinuationData x₀ g localModels)
    (y : (canonicalContinuationCover x₀).total) :
    C.toCanonicalCoverLocalTransitionContinuationData.centerAt y =
      C.centerAt (PathHomotopyUniversalCover.endpoint y)
        (PathHomotopyUniversalCover.pathClass y) :=
  rfl

/-- Lifting path-class continuation data preserves the selected Möbius representative.

%%handwave
name: Canonical lifting preserves the selected Möbius representative
statement: For a canonical-cover point $y$, the lifted representative is $M(π(y),[y])$, the representative assigned by the path-class data.
proof: This is the definition of the lifted Möbius field.
-/
@[simp]
theorem toCanonicalCoverLocalTransitionContinuationData_mobiusAt
    (C :
      PathClassLocalTransitionAnalyticContinuationData x₀ g localModels)
    (y : (canonicalContinuationCover x₀).total) :
    C.toCanonicalCoverLocalTransitionContinuationData.mobiusAt y =
      C.mobiusAt (PathHomotopyUniversalCover.endpoint y)
        (PathHomotopyUniversalCover.pathClass y) :=
  rfl

/-- Lifting path-class continuation data preserves the continuation neighborhood.

%%handwave
name: Canonical lifting preserves the continuation neighborhood
statement: For a cover point $y$, the lifted neighborhood is the neighborhood assigned by the path-class data to $(π(y),[y])$.
proof: This is the definition of the lifted neighborhood field.
-/
@[simp]
theorem toCanonicalCoverLocalTransitionContinuationData_neighborhoodAt
    (C :
      PathClassLocalTransitionAnalyticContinuationData x₀ g localModels)
    (y : (canonicalContinuationCover x₀).total) :
    C.toCanonicalCoverLocalTransitionContinuationData.neighborhoodAt y =
      C.neighborhoodAt (PathHomotopyUniversalCover.endpoint y)
        (PathHomotopyUniversalCover.pathClass y) :=
  rfl

end PathClassLocalTransitionAnalyticContinuationData

/--
PSL-valued loop equivariance for already constructed path-class
local-transition continuation data.
-/
structure PathClassLocalTransitionAnalyticContinuationEquivarianceDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (pathClassContinuation :
      PathClassLocalTransitionAnalyticContinuationData x₀ g localModels) where
  /-- PSL-valued real holonomy obtained from monodromy around loops. -/
  holonomy : RealHolonomyRepresentation X x₀
  /-- Loop action on path classes matches the PSL action on continued values. -/
  pathClass_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (x : X)
      (q : Path.Homotopic.Quotient x₀ x),
      pathClassContinuation.valueAt x
          (Path.Homotopic.Quotient.trans (FundamentalGroup.toPath γ⁻¹) q) =
        holonomy.upperHalfPlaneAction γ
          (pathClassContinuation.valueAt x q)

/--
PSL-valued path-class monodromy data for a local-transition atlas.
-/
structure PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Continuation data indexed by path-homotopy classes. -/
  pathClassContinuation :
    PathClassLocalTransitionAnalyticContinuationData x₀ g localModels
  /-- PSL-valued real holonomy obtained from monodromy around loops. -/
  holonomy : RealHolonomyRepresentation X x₀
  /-- Loop action on path classes matches the PSL action on continued values. -/
  pathClass_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (x : X)
      (q : Path.Homotopic.Quotient x₀ x),
      pathClassContinuation.valueAt x
          (Path.Homotopic.Quotient.trans (FundamentalGroup.toPath γ⁻¹) q) =
        holonomy.upperHalfPlaneAction γ
          (pathClassContinuation.valueAt x q)

namespace PathClassLocalTransitionAnalyticContinuationEquivarianceDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C : PathClassLocalTransitionAnalyticContinuationData x₀ g localModels}

/--
Path-class local-transition continuation plus PSL loop equivariance give the
PSL path-class monodromy package.
-/
def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (E :
      PathClassLocalTransitionAnalyticContinuationEquivarianceDataPSL C) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels where
  pathClassContinuation := C
  holonomy := E.holonomy
  pathClass_equivariant := E.pathClass_equivariant

end PathClassLocalTransitionAnalyticContinuationEquivarianceDataPSL

namespace PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
PSL path-class monodromy data give the PSL-valued reduced continuation fields
on the canonical cover.
-/
def toDerivedRegularityFieldsPSL
    (M :
      PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
        x₀ g localModels) :
    HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
      x₀ g localModels where
  dev := M.pathClassContinuation.dev
  holonomy := M.holonomy
  equivariant := by
    intro γ y
    simpa [PathClassLocalTransitionAnalyticContinuationData.dev,
      canonicalContinuationCover, SimplyConnectedCover.deckAction,
      PathHomotopyUniversalCover.deckHomeomorphism_apply,
      PathHomotopyUniversalCover.deckAction,
      PathHomotopyUniversalCover.endpoint,
      PathHomotopyUniversalCover.pathClass] using
      M.pathClass_equivariant γ (PathHomotopyUniversalCover.endpoint y)
        (PathHomotopyUniversalCover.pathClass y)
  agrees_with_local_models :=
    M.pathClassContinuation.toCanonicalCoverLocalTransitionContinuationData
      |>.agreesWithLocalTransitionModels

/-- The projective regularity fields derived from path-class monodromy retain its developing map.

%%handwave
name: Projective regularity derived from path-class monodromy preserves the developing map
statement: For projective path-class monodromy data $M$, the developing map in the derived projective regularity fields equals the developing map of the underlying path-class continuation data.
proof: The construction lifts the path-class data to the canonical cover and retains its developing map through projectivization and regularity derivation.
-/
@[simp]
theorem toDerivedRegularityFieldsPSL_dev
    (M :
      PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
        x₀ g localModels) :
    M.toDerivedRegularityFieldsPSL.dev =
      M.pathClassContinuation.dev :=
  rfl

end PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL

end HyperbolicMetric

end

end JJMath
