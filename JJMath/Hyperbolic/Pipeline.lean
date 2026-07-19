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

/--
%%handwave
name:
  A developing construction pipeline exists from existence of developing curvature pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing curvature pipeline exists, then a developing construction pipeline exists.
proof:
  Choose a curvature-provenance pipeline and forget only its curvature provenance; its aligned local constructions and continuation data form the required construction pipeline.
-/
theorem hasDevelopingConstructionPipeline_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasDevelopingConstructionPipeline x₀ :=
  h.elim fun P ↦ ⟨P.toHyperbolicDevelopingConstructionPipeline⟩

/--
%%handwave
name:
  Existence of curvature Liouville developing construction atlas is nonempty from existence of developing curvature pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing curvature pipeline exists, then the atlas of curvature-derived Liouville developing constructions is nonempty.
proof:
  Choose a curvature-provenance pipeline and take its stored curvature-derived Liouville developing-construction atlas.
-/
theorem nonempty_hasCurvatureLiouvilleDevelopingConstructionAtlas_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    Nonempty g.HasCurvatureLiouvilleDevelopingConstructionAtlas :=
  h.elim fun P ↦ ⟨P.localCurvatureConstructions⟩

/--
%%handwave
name:
  A curvature Liouville formula atlas exists from existence of developing curvature pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing curvature pipeline exists, then a curvature Liouville formula atlas exists.
proof:
  Choose the stored curvature-derived developing-construction atlas, then forget its developing maps to retain the curvature Liouville formulas.
-/
theorem hasCurvatureLiouvilleFormulaAtlas_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasCurvatureLiouvilleFormulaAtlas :=
  (nonempty_hasCurvatureLiouvilleDevelopingConstructionAtlas_of_hasDevelopingCurvaturePipeline h).elim
    fun H ↦ hasCurvatureLiouvilleFormulaAtlas_of_hasCurvatureLiouvilleDevelopingConstructionAtlas H

/--
%%handwave
name:
  A developing pipeline exists from existence of developing construction pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing construction pipeline exists, then a developing pipeline exists.
proof:
  Choose an aligned construction pipeline and forget the alignment provenance, retaining its local solutions and continuation data.
-/
theorem hasDevelopingPipeline_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.HasDevelopingPipeline x₀ :=
  h.elim fun P ↦ ⟨P.toHyperbolicDevelopingPipeline⟩

/--
%%handwave
name:
  A developing pipeline exists from existence of developing curvature pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing curvature pipeline exists, then a developing pipeline exists.
proof:
  First use [a curvature-provenance pipeline yields a developing-construction pipeline](lean:JJMath.HyperbolicMetric.hasDevelopingConstructionPipeline_of_hasDevelopingCurvaturePipeline), then [a developing-construction pipeline yields a developing pipeline](lean:JJMath.HyperbolicMetric.hasDevelopingPipeline_of_hasDevelopingConstructionPipeline).
-/
theorem hasDevelopingPipeline_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasDevelopingPipeline x₀ :=
  hasDevelopingPipeline_of_hasDevelopingConstructionPipeline
    (hasDevelopingConstructionPipeline_of_hasDevelopingCurvaturePipeline h)

/--
%%handwave
name:
  A local Liouville developing construction atlas exists from existence of developing construction pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing construction pipeline exists, then a local Liouville developing construction atlas exists.
proof:
  Choose a construction pipeline and take its stored atlas of aligned local Liouville developing constructions.
-/
theorem hasLocalLiouvilleDevelopingConstructionAtlas_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.HasLocalLiouvilleDevelopingConstructionAtlas :=
  h.elim fun P ↦ ⟨P.localConstructions⟩

/--
%%handwave
name:
  A local Liouville developing construction atlas exists from existence of developing curvature pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing curvature pipeline exists, then a local Liouville developing construction atlas exists.
proof:
  Forget curvature provenance and apply [a developing-construction pipeline yields an atlas of aligned local Liouville constructions](lean:JJMath.HyperbolicMetric.hasLocalLiouvilleDevelopingConstructionAtlas_of_hasDevelopingConstructionPipeline).
-/
theorem hasLocalLiouvilleDevelopingConstructionAtlas_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasLocalLiouvilleDevelopingConstructionAtlas :=
  hasLocalLiouvilleDevelopingConstructionAtlas_of_hasDevelopingConstructionPipeline
    (hasDevelopingConstructionPipeline_of_hasDevelopingCurvaturePipeline h)

/--
%%handwave
name:
  A local Liouville metric formula atlas exists from existence of developing pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing pipeline exists, then a local Liouville metric formula atlas exists.
proof:
  Choose a developing pipeline, take its local Liouville developing solutions, and forget the developing maps to obtain their metric formulas.
-/
theorem hasLocalLiouvilleMetricFormulaAtlas_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.HasLocalLiouvilleMetricFormulaAtlas :=
  h.elim fun P ↦
    hasLocalLiouvilleMetricFormulaAtlas_of_hasLocalLiouvilleDevelopingSolutionAtlas
      ⟨P.localSolutions⟩

/--
%%handwave
name:
  A local Liouville metric formula atlas exists from existence of developing construction pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing construction pipeline exists, then a local Liouville metric formula atlas exists.
proof:
  Extract the aligned local constructions and apply [an aligned local Liouville construction atlas yields a local Liouville metric-formula atlas](lean:JJMath.HyperbolicMetric.hasLocalLiouvilleMetricFormulaAtlas_of_hasLocalLiouvilleDevelopingConstructionAtlas).
-/
theorem hasLocalLiouvilleMetricFormulaAtlas_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.HasLocalLiouvilleMetricFormulaAtlas :=
  hasLocalLiouvilleMetricFormulaAtlas_of_hasLocalLiouvilleDevelopingConstructionAtlas
    (hasLocalLiouvilleDevelopingConstructionAtlas_of_hasDevelopingConstructionPipeline h)

/--
%%handwave
name:
  A local Liouville metric formula atlas exists from existence of developing curvature pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing curvature pipeline exists, then a local Liouville metric formula atlas exists.
proof:
  Extract the curvature Liouville formula atlas and apply [a curvature Liouville formula atlas yields a local Liouville metric-formula atlas](lean:JJMath.HyperbolicMetric.hasLocalLiouvilleMetricFormulaAtlas_of_hasCurvatureLiouvilleFormulaAtlas).
-/
theorem hasLocalLiouvilleMetricFormulaAtlas_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasLocalLiouvilleMetricFormulaAtlas :=
  hasLocalLiouvilleMetricFormulaAtlas_of_hasCurvatureLiouvilleFormulaAtlas
    (hasCurvatureLiouvilleFormulaAtlas_of_hasDevelopingCurvaturePipeline h)

/--
%%handwave
name:
  A coordinate upper half plane pullback formula atlas exists from existence of developing pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing pipeline exists, then a coordinate upper half plane pullback formula atlas exists.
proof:
  Choose the pipeline’s local developing solutions and retain their coordinate pullback formulas for the Poincaré metric.
-/
theorem hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas :=
  h.elim fun P ↦
    hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasLocalLiouvilleDevelopingSolutionAtlas
      ⟨P.localSolutions⟩

/--
%%handwave
name:
  A coordinate upper half plane pullback formula atlas exists from existence of developing construction pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing construction pipeline exists, then a coordinate upper half plane pullback formula atlas exists.
proof:
  Extract the aligned construction atlas and retain the coordinate upper-half-plane pullback formula from each construction.
-/
theorem hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas :=
  hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasLocalLiouvilleDevelopingConstructionAtlas
    (hasLocalLiouvilleDevelopingConstructionAtlas_of_hasDevelopingConstructionPipeline h)

/--
%%handwave
name:
  A coordinate upper half plane pullback formula atlas exists from existence of developing curvature pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing curvature pipeline exists, then a coordinate upper half plane pullback formula atlas exists.
proof:
  Choose the stored curvature-derived developing constructions and forget both curvature and alignment provenance, retaining their coordinate pullback formulas.
-/
theorem hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas :=
  (nonempty_hasCurvatureLiouvilleDevelopingConstructionAtlas_of_hasDevelopingCurvaturePipeline h).elim
    fun H ↦
      hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasCurvatureLiouvilleDevelopingConstructionAtlas H

/--
%%handwave
name:
  A upper half plane local models exists from existence of developing pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing pipeline exists, then an atlas of local upper-half-plane models exists.
proof:
  Choose the local developing solutions stored by the pipeline and forget their Liouville-formula provenance, retaining the local maps to $\mathbb H$.
-/
theorem hasUpperHalfPlaneLocalModels_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.HasUpperHalfPlaneLocalModels :=
  h.elim fun P ↦
    hasUpperHalfPlaneLocalModels_of_hasLocalLiouvilleDevelopingSolutionAtlas
      ⟨P.localSolutions⟩

/--
%%handwave
name:
  A upper half plane local models exists from existence of developing construction pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing construction pipeline exists, then an atlas of local upper-half-plane models exists.
proof:
  Extract the aligned constructions and apply [an aligned local Liouville construction atlas yields an atlas of local upper-half-plane models](lean:JJMath.HyperbolicMetric.hasUpperHalfPlaneLocalModels_of_hasLocalLiouvilleDevelopingConstructionAtlas).
-/
theorem hasUpperHalfPlaneLocalModels_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.HasUpperHalfPlaneLocalModels :=
  hasUpperHalfPlaneLocalModels_of_hasLocalLiouvilleDevelopingConstructionAtlas
    (hasLocalLiouvilleDevelopingConstructionAtlas_of_hasDevelopingConstructionPipeline h)

/--
%%handwave
name:
  A upper half plane local models exists from existence of developing curvature pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing curvature pipeline exists, then an atlas of local upper-half-plane models exists.
proof:
  Choose the curvature-derived local constructions and forget their curvature and Liouville provenance, leaving an atlas of local maps to $\mathbb H$.
-/
theorem hasUpperHalfPlaneLocalModels_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasUpperHalfPlaneLocalModels :=
  (nonempty_hasCurvatureLiouvilleDevelopingConstructionAtlas_of_hasDevelopingCurvaturePipeline h).elim
    fun H ↦ hasUpperHalfPlaneLocalModels_of_hasCurvatureLiouvilleDevelopingConstructionAtlas H

/--
%%handwave
name:
  A developing continuation data exists from existence of developing pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing pipeline exists, then analytic-continuation data for its local developing maps exist.
proof:
  Choose a developing pipeline and take its stored analytic-continuation data.
-/
theorem hasDevelopingContinuationData_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.HasDevelopingContinuationData x₀ :=
  h.elim fun P ↦ ⟨P.toHyperbolicDevelopingContinuationData⟩

/--
%%handwave
name:
  A local model continuation pipeline exists from existence of developing pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing pipeline exists, then a local model continuation pipeline exists.
proof:
  Choose a developing pipeline and pair its local-model atlas with the stored continuation data; the recorded compatibility equality is unchanged.
-/
theorem hasLocalModelContinuationPipeline_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.HasLocalModelContinuationPipeline x₀ :=
  h.elim fun P ↦ ⟨P.toHyperbolicLocalModelContinuationPipeline⟩

/--
%%handwave
name:
  A local model continuation pipeline exists from existence of developing construction pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing construction pipeline exists, then a local model continuation pipeline exists.
proof:
  Forget the aligned-construction provenance and apply [a developing pipeline yields a local-model continuation pipeline](lean:JJMath.HyperbolicMetric.hasLocalModelContinuationPipeline_of_hasDevelopingPipeline).
-/
theorem hasLocalModelContinuationPipeline_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.HasLocalModelContinuationPipeline x₀ :=
  hasLocalModelContinuationPipeline_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingConstructionPipeline h)

/--
%%handwave
name:
  A local model continuation pipeline exists from existence of developing curvature pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing curvature pipeline exists, then a local model continuation pipeline exists.
proof:
  Forget curvature and construction provenance and apply [a developing pipeline yields a local-model continuation pipeline](lean:JJMath.HyperbolicMetric.hasLocalModelContinuationPipeline_of_hasDevelopingPipeline).
-/
theorem hasLocalModelContinuationPipeline_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasLocalModelContinuationPipeline x₀ :=
  hasLocalModelContinuationPipeline_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingCurvaturePipeline h)

/--
%%handwave
name:
  A local Liouville developing solution atlas exists from existence of developing pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing pipeline exists, then a local Liouville developing solution atlas exists.
proof:
  Choose a developing pipeline and take its stored atlas of local Liouville developing solutions.
-/
theorem hasLocalLiouvilleDevelopingSolutionAtlas_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.HasLocalLiouvilleDevelopingSolutionAtlas :=
  h.elim fun P ↦ ⟨P.localSolutions⟩

/--
%%handwave
name:
  A local Liouville developing solution atlas exists from existence of developing construction pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing construction pipeline exists, then a local Liouville developing solution atlas exists.
proof:
  Forget the aligned-construction provenance and take the local Liouville developing solutions of the resulting pipeline.
-/
theorem hasLocalLiouvilleDevelopingSolutionAtlas_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.HasLocalLiouvilleDevelopingSolutionAtlas :=
  hasLocalLiouvilleDevelopingSolutionAtlas_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingConstructionPipeline h)

/--
%%handwave
name:
  A local Liouville developing solution atlas exists from existence of developing curvature pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing curvature pipeline exists, then a local Liouville developing solution atlas exists.
proof:
  Forget curvature and alignment provenance and take the local Liouville developing solutions of the resulting pipeline.
-/
theorem hasLocalLiouvilleDevelopingSolutionAtlas_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasLocalLiouvilleDevelopingSolutionAtlas :=
  hasLocalLiouvilleDevelopingSolutionAtlas_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingCurvaturePipeline h)

/--
%%handwave
name:
  The metric admits lifted developing map from existence of developing pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing pipeline exists, then the metric admits lifted developing map.
proof:
  Choose a developing pipeline and apply its continuation data to its local solutions, obtaining the stored lifted developing map.
-/
theorem admitsLiftedDevelopingMap_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  h.elim fun P ↦ ⟨P.toLiftedHyperbolicDevelopingMap⟩

/--
%%handwave
name:
  The metric admits lifted developing map from existence of developing construction pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing construction pipeline exists, then the metric admits lifted developing map.
proof:
  Forget the aligned-construction provenance and apply [a developing pipeline produces a lifted developing map](lean:JJMath.HyperbolicMetric.admitsLiftedDevelopingMap_of_hasDevelopingPipeline).
-/
theorem admitsLiftedDevelopingMap_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  admitsLiftedDevelopingMap_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingConstructionPipeline h)

/--
%%handwave
name:
  The metric admits lifted developing map from existence of developing curvature pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing curvature pipeline exists, then the metric admits lifted developing map.
proof:
  Forget curvature and alignment provenance and apply [a developing pipeline produces a lifted developing map](lean:JJMath.HyperbolicMetric.admitsLiftedDevelopingMap_of_hasDevelopingPipeline).
-/
theorem admitsLiftedDevelopingMap_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  admitsLiftedDevelopingMap_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingCurvaturePipeline h)

/--
%%handwave
name:
  The metric admits developing map from existence of developing pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing pipeline exists, then the metric admits developing map.
proof:
  Choose a developing pipeline and project the holonomy of its lifted developing map from $\mathrm{SL}_2(\mathbb R)$ to $\mathrm{PSL}_2(\mathbb R)$.
-/
theorem admitsDevelopingMap_of_hasDevelopingPipeline
    {x₀ : X} {g : HyperbolicMetric X} (h : g.HasDevelopingPipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  h.elim fun P ↦ ⟨P.toHyperbolicDevelopingMap⟩

/--
%%handwave
name:
  The metric admits developing map from existence of developing construction pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing construction pipeline exists, then the metric admits developing map.
proof:
  Forget the aligned-construction provenance and apply [a developing pipeline produces a $\mathrm{PSL}_2(\mathbb R)$-equivariant developing map](lean:JJMath.HyperbolicMetric.admitsDevelopingMap_of_hasDevelopingPipeline).
-/
theorem admitsDevelopingMap_of_hasDevelopingConstructionPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingConstructionPipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingConstructionPipeline h)

/--
%%handwave
name:
  The metric admits developing map from existence of developing curvature pipeline
statement:
  For a hyperbolic metric $g$ on a Riemann surface and a basepoint $x_0$, if a developing curvature pipeline exists, then the metric admits developing map.
proof:
  Forget curvature and alignment provenance and apply [a developing pipeline produces a $\mathrm{PSL}_2(\mathbb R)$-equivariant developing map](lean:JJMath.HyperbolicMetric.admitsDevelopingMap_of_hasDevelopingPipeline).
-/
theorem admitsDevelopingMap_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_hasDevelopingPipeline
    (hasDevelopingPipeline_of_hasDevelopingCurvaturePipeline h)

end HyperbolicMetric

end

end JJMath
