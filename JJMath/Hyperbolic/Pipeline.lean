import JJMath.Hyperbolic.LocalFormula

/-!
# Local-to-global pipeline for hyperbolic developing maps

This file ties together the two major pieces of the developing-map theorem:

1. local Liouville/developing solutions, giving local maps to `ℍ`;
2. analytic continuation of those local maps on the simply connected cover.

The resulting package immediately produces the lifted and `PSL(2, ℝ)`-valued
developing-map targets.
-/

namespace JJMath

noncomputable section

/--
The full local-to-global package for constructing a developing map from a
hyperbolic metric.

The field `continuation_uses_local_solutions` records that the analytic
continuation data is built from the local models underlying the Liouville
solutions.
-/
structure HyperbolicDevelopingPipeline (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] (x₀ : X)
    (g : HyperbolicMetric X) where
  /-- Local PDE/developing solutions. -/
  localSolutions : LocalLiouvilleDevelopingSolutionAtlas X g
  /-- Analytic continuation and monodromy of the underlying local models. -/
  continuationData : HyperbolicDevelopingContinuationData X x₀ g
  /-- The continuation data uses the local models coming from `localSolutions`. -/
  continuation_uses_local_solutions :
    continuationData.localModels = localSolutions.toHyperbolicLocalModelAtlas

namespace HyperbolicDevelopingPipeline

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- Forget the full pipeline and keep only its local-model atlas. -/
def toHyperbolicLocalModelAtlas (P : HyperbolicDevelopingPipeline X x₀ g) :
    HyperbolicLocalModelAtlas X g :=
  P.localSolutions.toHyperbolicLocalModelAtlas

/-- Forget local PDE provenance and keep the local-model continuation package. -/
def toHyperbolicLocalModelContinuationPipeline
    (P : HyperbolicDevelopingPipeline X x₀ g) :
    HyperbolicLocalModelContinuationPipeline X x₀ g where
  localModels := P.localSolutions.toHyperbolicLocalModelAtlas
  continuationData := P.continuationData
  continuation_uses_localModels := P.continuation_uses_local_solutions

/-- Forget the full pipeline and keep only the continuation data. -/
def toHyperbolicDevelopingContinuationData
    (P : HyperbolicDevelopingPipeline X x₀ g) :
    HyperbolicDevelopingContinuationData X x₀ g :=
  P.continuationData

/-- The lifted developing map produced by the pipeline. -/
def toLiftedHyperbolicDevelopingMap
    (P : HyperbolicDevelopingPipeline X x₀ g) :
    LiftedHyperbolicDevelopingMap X x₀ g :=
  P.continuationData.toLiftedHyperbolicDevelopingMap

/-- The ordinary `PSL(2, ℝ)` developing map produced by the pipeline. -/
def toHyperbolicDevelopingMap (P : HyperbolicDevelopingPipeline X x₀ g) :
    HyperbolicDevelopingMap X x₀ g :=
  P.toLiftedHyperbolicDevelopingMap.toHyperbolicDevelopingMap

end HyperbolicDevelopingPipeline

/--
The full local-to-global package using the aligned local construction atlas.

This is a refinement of `HyperbolicDevelopingPipeline`: it remembers the step
that aligns metric Liouville formulas with coordinate Poincare pullback
formulas before analytic continuation.
-/
structure HyperbolicDevelopingConstructionPipeline (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] (x₀ : X)
    (g : HyperbolicMetric X) where
  /-- Local aligned constructions of Liouville developing solutions. -/
  localConstructions : LocalLiouvilleDevelopingConstructionAtlas X g
  /-- Analytic continuation and monodromy of the underlying local models. -/
  continuationData : HyperbolicDevelopingContinuationData X x₀ g
  /-- The continuation data uses the local models coming from `localConstructions`. -/
  continuation_uses_local_constructions :
    continuationData.localModels =
      localConstructions.toLocalLiouvilleDevelopingSolutionAtlas.toHyperbolicLocalModelAtlas

namespace HyperbolicDevelopingConstructionPipeline

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- Forget aligned-construction provenance and keep the local developing solutions. -/
def toLocalLiouvilleDevelopingSolutionAtlas
    (P : HyperbolicDevelopingConstructionPipeline X x₀ g) :
    LocalLiouvilleDevelopingSolutionAtlas X g :=
  P.localConstructions.toLocalLiouvilleDevelopingSolutionAtlas

/-- Forget to the existing full developing pipeline. -/
def toHyperbolicDevelopingPipeline
    (P : HyperbolicDevelopingConstructionPipeline X x₀ g) :
    HyperbolicDevelopingPipeline X x₀ g where
  localSolutions := P.toLocalLiouvilleDevelopingSolutionAtlas
  continuationData := P.continuationData
  continuation_uses_local_solutions := P.continuation_uses_local_constructions

/-- Forget local PDE provenance and keep the local-model continuation package. -/
def toHyperbolicLocalModelContinuationPipeline
    (P : HyperbolicDevelopingConstructionPipeline X x₀ g) :
    HyperbolicLocalModelContinuationPipeline X x₀ g :=
  P.toHyperbolicDevelopingPipeline.toHyperbolicLocalModelContinuationPipeline

/-- The lifted developing map produced by the construction pipeline. -/
def toLiftedHyperbolicDevelopingMap
    (P : HyperbolicDevelopingConstructionPipeline X x₀ g) :
    LiftedHyperbolicDevelopingMap X x₀ g :=
  P.toHyperbolicDevelopingPipeline.toLiftedHyperbolicDevelopingMap

/-- The ordinary `PSL(2, ℝ)` developing map produced by the construction pipeline. -/
def toHyperbolicDevelopingMap
    (P : HyperbolicDevelopingConstructionPipeline X x₀ g) :
    HyperbolicDevelopingMap X x₀ g :=
  P.toHyperbolicDevelopingPipeline.toHyperbolicDevelopingMap

end HyperbolicDevelopingConstructionPipeline

/--
The full local-to-global package with curvature provenance.

This refines `HyperbolicDevelopingConstructionPipeline` by remembering that the
local Liouville formulas solved by the aligned constructions came from the
curvature `-1` condition of the hyperbolic metric.
-/
structure HyperbolicDevelopingCurvaturePipeline (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] (x₀ : X)
    (g : HyperbolicMetric X) where
  /-- Curvature-derived local formulas solved by aligned maps to `ℍ`. -/
  localCurvatureConstructions : g.HasCurvatureLiouvilleDevelopingConstructionAtlas
  /-- Analytic continuation and monodromy of the underlying local models. -/
  continuationData : HyperbolicDevelopingContinuationData X x₀ g
  /-- The continuation data uses the local models coming from the local constructions. -/
  continuation_uses_curvature_constructions :
    continuationData.localModels =
      (LocalLiouvilleDevelopingConstructionAtlas.toLocalLiouvilleDevelopingSolutionAtlas
        localCurvatureConstructions.developingConstructionAtlas).toHyperbolicLocalModelAtlas

namespace HyperbolicDevelopingCurvaturePipeline

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- Forget curvature provenance and keep the aligned construction atlas. -/
def toLocalLiouvilleDevelopingConstructionAtlas
    (P : HyperbolicDevelopingCurvaturePipeline X x₀ g) :
    LocalLiouvilleDevelopingConstructionAtlas X g :=
  P.localCurvatureConstructions.developingConstructionAtlas

/-- Forget curvature provenance and keep the construction-level developing pipeline. -/
def toHyperbolicDevelopingConstructionPipeline
    (P : HyperbolicDevelopingCurvaturePipeline X x₀ g) :
    HyperbolicDevelopingConstructionPipeline X x₀ g where
  localConstructions := P.toLocalLiouvilleDevelopingConstructionAtlas
  continuationData := P.continuationData
  continuation_uses_local_constructions :=
    P.continuation_uses_curvature_constructions

/-- Forget to the ordinary developing pipeline. -/
def toHyperbolicDevelopingPipeline
    (P : HyperbolicDevelopingCurvaturePipeline X x₀ g) :
    HyperbolicDevelopingPipeline X x₀ g :=
  P.toHyperbolicDevelopingConstructionPipeline.toHyperbolicDevelopingPipeline

/-- The lifted developing map produced by the curvature pipeline. -/
def toLiftedHyperbolicDevelopingMap
    (P : HyperbolicDevelopingCurvaturePipeline X x₀ g) :
    LiftedHyperbolicDevelopingMap X x₀ g :=
  P.toHyperbolicDevelopingPipeline.toLiftedHyperbolicDevelopingMap

/-- The ordinary `PSL(2, ℝ)` developing map produced by the curvature pipeline. -/
def toHyperbolicDevelopingMap
    (P : HyperbolicDevelopingCurvaturePipeline X x₀ g) :
    HyperbolicDevelopingMap X x₀ g :=
  P.toHyperbolicDevelopingPipeline.toHyperbolicDevelopingMap

end HyperbolicDevelopingCurvaturePipeline

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/--
Target full theorem package: the hyperbolic metric has local Liouville
developing solutions and these analytically continue on the universal cover.
-/
def HasDevelopingPipeline (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (HyperbolicDevelopingPipeline X x₀ g)

/--
Target full theorem package through the aligned local construction atlas.
-/
def HasDevelopingConstructionPipeline (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (HyperbolicDevelopingConstructionPipeline X x₀ g)

/--
Target full theorem package with curvature provenance.
-/
def HasDevelopingCurvaturePipeline (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (HyperbolicDevelopingCurvaturePipeline X x₀ g)

theorem hasDevelopingConstructionPipeline_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasDevelopingConstructionPipeline x₀ :=
  h.elim fun P ↦ ⟨P.toHyperbolicDevelopingConstructionPipeline⟩

theorem nonempty_hasCurvatureLiouvilleDevelopingConstructionAtlas_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    Nonempty g.HasCurvatureLiouvilleDevelopingConstructionAtlas :=
  h.elim fun P ↦ ⟨P.localCurvatureConstructions⟩

theorem hasCurvatureLiouvilleFormulaAtlas_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasCurvatureLiouvilleFormulaAtlas :=
  (nonempty_hasCurvatureLiouvilleDevelopingConstructionAtlas_of_hasDevelopingCurvaturePipeline h).elim
    fun H ↦ hasCurvatureLiouvilleFormulaAtlas_of_hasCurvatureLiouvilleDevelopingConstructionAtlas H

theorem hasDevelopingPipeline_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.HasDevelopingPipeline x₀ :=
  h.elim fun P ↦ ⟨P.toHyperbolicDevelopingPipeline⟩

theorem hasDevelopingPipeline_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasDevelopingPipeline x₀ :=
  hasDevelopingPipeline_of_hasDevelopingConstructionPipeline
    (hasDevelopingConstructionPipeline_of_hasDevelopingCurvaturePipeline h)

theorem hasLocalLiouvilleDevelopingConstructionAtlas_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.HasLocalLiouvilleDevelopingConstructionAtlas :=
  h.elim fun P ↦ ⟨P.localConstructions⟩

theorem hasLocalLiouvilleDevelopingConstructionAtlas_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasLocalLiouvilleDevelopingConstructionAtlas :=
  hasLocalLiouvilleDevelopingConstructionAtlas_of_hasDevelopingConstructionPipeline
    (hasDevelopingConstructionPipeline_of_hasDevelopingCurvaturePipeline h)

theorem hasLocalLiouvilleMetricFormulaAtlas_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.HasLocalLiouvilleMetricFormulaAtlas :=
  h.elim fun P ↦
    hasLocalLiouvilleMetricFormulaAtlas_of_hasLocalLiouvilleDevelopingSolutionAtlas
      ⟨P.localSolutions⟩

theorem hasLocalLiouvilleMetricFormulaAtlas_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.HasLocalLiouvilleMetricFormulaAtlas :=
  hasLocalLiouvilleMetricFormulaAtlas_of_hasLocalLiouvilleDevelopingConstructionAtlas
    (hasLocalLiouvilleDevelopingConstructionAtlas_of_hasDevelopingConstructionPipeline h)

theorem hasLocalLiouvilleMetricFormulaAtlas_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasLocalLiouvilleMetricFormulaAtlas :=
  hasLocalLiouvilleMetricFormulaAtlas_of_hasCurvatureLiouvilleFormulaAtlas
    (hasCurvatureLiouvilleFormulaAtlas_of_hasDevelopingCurvaturePipeline h)

theorem hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas :=
  h.elim fun P ↦
    hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasLocalLiouvilleDevelopingSolutionAtlas
      ⟨P.localSolutions⟩

theorem hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas :=
  hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasLocalLiouvilleDevelopingConstructionAtlas
    (hasLocalLiouvilleDevelopingConstructionAtlas_of_hasDevelopingConstructionPipeline h)

theorem hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas :=
  (nonempty_hasCurvatureLiouvilleDevelopingConstructionAtlas_of_hasDevelopingCurvaturePipeline h).elim
    fun H ↦
      hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasCurvatureLiouvilleDevelopingConstructionAtlas H

theorem hasUpperHalfPlaneLocalModels_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.HasUpperHalfPlaneLocalModels :=
  h.elim fun P ↦
    hasUpperHalfPlaneLocalModels_of_hasLocalLiouvilleDevelopingSolutionAtlas
      ⟨P.localSolutions⟩

theorem hasUpperHalfPlaneLocalModels_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.HasUpperHalfPlaneLocalModels :=
  hasUpperHalfPlaneLocalModels_of_hasLocalLiouvilleDevelopingConstructionAtlas
    (hasLocalLiouvilleDevelopingConstructionAtlas_of_hasDevelopingConstructionPipeline h)

theorem hasUpperHalfPlaneLocalModels_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasUpperHalfPlaneLocalModels :=
  (nonempty_hasCurvatureLiouvilleDevelopingConstructionAtlas_of_hasDevelopingCurvaturePipeline h).elim
    fun H ↦ hasUpperHalfPlaneLocalModels_of_hasCurvatureLiouvilleDevelopingConstructionAtlas H

theorem hasDevelopingContinuationData_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.HasDevelopingContinuationData x₀ :=
  h.elim fun P ↦ ⟨P.toHyperbolicDevelopingContinuationData⟩

theorem hasLocalModelContinuationPipeline_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.HasLocalModelContinuationPipeline x₀ :=
  h.elim fun P ↦ ⟨P.toHyperbolicLocalModelContinuationPipeline⟩

theorem hasLocalModelContinuationPipeline_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.HasLocalModelContinuationPipeline x₀ :=
  hasLocalModelContinuationPipeline_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingConstructionPipeline h)

theorem hasLocalModelContinuationPipeline_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasLocalModelContinuationPipeline x₀ :=
  hasLocalModelContinuationPipeline_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingCurvaturePipeline h)

theorem hasLocalLiouvilleDevelopingSolutionAtlas_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.HasLocalLiouvilleDevelopingSolutionAtlas :=
  h.elim fun P ↦ ⟨P.localSolutions⟩

theorem hasLocalLiouvilleDevelopingSolutionAtlas_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.HasLocalLiouvilleDevelopingSolutionAtlas :=
  hasLocalLiouvilleDevelopingSolutionAtlas_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingConstructionPipeline h)

theorem hasLocalLiouvilleDevelopingSolutionAtlas_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasLocalLiouvilleDevelopingSolutionAtlas :=
  hasLocalLiouvilleDevelopingSolutionAtlas_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingCurvaturePipeline h)

theorem admitsLiftedDevelopingMap_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  h.elim fun P ↦ ⟨P.toLiftedHyperbolicDevelopingMap⟩

theorem admitsLiftedDevelopingMap_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  admitsLiftedDevelopingMap_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingConstructionPipeline h)

theorem admitsLiftedDevelopingMap_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  admitsLiftedDevelopingMap_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingCurvaturePipeline h)

theorem admitsDevelopingMap_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  h.elim fun P ↦ ⟨P.toHyperbolicDevelopingMap⟩

theorem admitsDevelopingMap_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingConstructionPipeline h)

theorem admitsDevelopingMap_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingCurvaturePipeline h)

end HyperbolicMetric

end

end JJMath
