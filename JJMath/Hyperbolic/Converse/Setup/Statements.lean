import JJMath.Hyperbolic.ProjectiveStructure
import JJMath.Hyperbolic.Schwarzian
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Split partial-converse setup declarations
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/--
The local curvature-solving milestone of the partial converse.

This is the first hard analytic step: solve the curvature-derived local
Liouville problem by local maps to `ℍ`.
-/
structure CurvatureLocalSolvingPackage (g : HyperbolicMetric X) where
  /-- Curvature-derived local formulas solved by maps to `ℍ`. -/
  localCurvatureConstructions : g.HasCurvatureLiouvilleDevelopingConstructionAtlas
  /-- Curvature-derived Liouville formula charts. -/
  curvatureFormulaAtlas : g.HasCurvatureLiouvilleFormulaAtlas
  /-- Coordinate Poincare pullback formula charts. -/
  coordinatePullbackFormulaAtlas : g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas
  /-- Local maps to the upper half-plane whose pullback metric is `g`. -/
  upperHalfPlaneLocalModels : g.HasUpperHalfPlaneLocalModels

/-- Prop-level target for the local curvature-solving package. -/
def AdmitsCurvatureLocalSolvingPackage (g : HyperbolicMetric X) : Prop :=
  Nonempty (g.CurvatureLocalSolvingPackage)

/--
Assemble the local curvature-solving package from the strongest local
construction target.
-/
def curvatureLocalSolvingPackage_of_hasCurvatureLiouvilleDevelopingConstructionAtlas
    {g : HyperbolicMetric X}
    (h : g.HasCurvatureLiouvilleDevelopingConstructionAtlas) :
    g.CurvatureLocalSolvingPackage where
  localCurvatureConstructions := h
  curvatureFormulaAtlas :=
    hasCurvatureLiouvilleFormulaAtlas_of_hasCurvatureLiouvilleDevelopingConstructionAtlas h
  coordinatePullbackFormulaAtlas :=
    hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasCurvatureLiouvilleDevelopingConstructionAtlas h
  upperHalfPlaneLocalModels :=
    hasUpperHalfPlaneLocalModels_of_hasCurvatureLiouvilleDevelopingConstructionAtlas h

omit [RiemannSurface X] in
theorem admitsCurvatureLocalSolvingPackage_of_hasCurvatureLiouvilleDevelopingConstructionAtlas
    {g : HyperbolicMetric X}
    (h : g.HasCurvatureLiouvilleDevelopingConstructionAtlas) :
    g.AdmitsCurvatureLocalSolvingPackage :=
  ⟨curvatureLocalSolvingPackage_of_hasCurvatureLiouvilleDevelopingConstructionAtlas h⟩

omit [RiemannSurface X] in
theorem hasUpperHalfPlaneLocalModels_of_admitsCurvatureLocalSolvingPackage
    {g : HyperbolicMetric X}
    (h : g.AdmitsCurvatureLocalSolvingPackage) :
    g.HasUpperHalfPlaneLocalModels :=
  h.elim fun H ↦ H.upperHalfPlaneLocalModels

/--
The analytic hyperbolic part of the partial converse.

This stops before projectivization: it says that the curvature-derived local
developing constructions have been analytically continued on the simply
connected cover.
-/
structure HyperbolicDevelopingAnalyticData (x₀ : X) (g : HyperbolicMetric X) where
  /-- The local curvature-solving package used as input to continuation. -/
  localSolvingPackage : g.AdmitsCurvatureLocalSolvingPackage
  /-- Curvature-derived local formulas solved by maps to `ℍ`. -/
  localCurvatureConstructions : g.HasCurvatureLiouvilleDevelopingConstructionAtlas
  /-- Analytic continuation of the local models on the simply connected cover. -/
  continuationData : HyperbolicDevelopingContinuationData X x₀ g
  /-- The continuation data uses the local models obtained from the local constructions. -/
  continuation_uses_curvature_constructions :
    continuationData.localModels =
      (LocalLiouvilleDevelopingConstructionAtlas.toLocalLiouvilleDevelopingSolutionAtlas
        localCurvatureConstructions.developingConstructionAtlas).toHyperbolicLocalModelAtlas

/-- Prop-level target for the analytic hyperbolic part of the partial converse. -/
def HasHyperbolicDevelopingAnalyticData (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (g.HyperbolicDevelopingAnalyticData x₀)

/--
Output package for the analytic hyperbolic milestone of the partial converse.

This is the stage before the projective atlas is constructed: local curvature
solving plus analytic continuation has already produced the hyperbolic
developing map.
-/
structure HyperbolicDevelopingAnalyticPackage (x₀ : X) (g : HyperbolicMetric X) where
  /-- The local curvature-solving package. -/
  localSolvingPackage : g.AdmitsCurvatureLocalSolvingPackage
  /-- Curvature-derived Liouville formula charts. -/
  curvatureFormulaAtlas : g.HasCurvatureLiouvilleFormulaAtlas
  /-- Coordinate Poincare pullback formula charts. -/
  coordinatePullbackFormulaAtlas : g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas
  /-- Local maps to the upper half-plane whose pullback metric is `g`. -/
  upperHalfPlaneLocalModels : g.HasUpperHalfPlaneLocalModels
  /-- The curvature-aware developing pipeline. -/
  developingCurvaturePipeline : g.HasDevelopingCurvaturePipeline x₀
  /-- A lifted developing map with `SL(2, ℝ)` holonomy. -/
  liftedDevelopingMap : g.AdmitsLiftedDevelopingMap x₀
  /-- The ordinary developing map with `PSL(2, ℝ)` holonomy. -/
  developingMap : g.AdmitsDevelopingMap x₀

/-- Prop-level target for the analytic hyperbolic output package. -/
def AdmitsHyperbolicDevelopingAnalyticPackage
    (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (g.HyperbolicDevelopingAnalyticPackage x₀)

/--
Projectivized analytic output before constructing the projective atlas on `X`.

This packages the hyperbolic analytic milestone together with the
Riemann-sphere-valued developing map obtained by composing with
`ℍ → ℂP¹`.
-/
structure ProjectivizedAnalyticPackage (x₀ : X) (g : HyperbolicMetric X) where
  /-- The analytic hyperbolic package before projectivization. -/
  analyticPackage : g.AdmitsHyperbolicDevelopingAnalyticPackage x₀
  /-- The projectivized developing map to the Riemann sphere. -/
  projectivizedDevelopingMap : g.AdmitsProjectivizedDevelopingMap x₀

/-- Prop-level target for the projectivized analytic output package. -/
def AdmitsProjectivizedAnalyticPackage
    (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (g.ProjectivizedAnalyticPackage x₀)

/--
Output package for the projective-atlas construction stage.

This is the stage after projectivizing the developing map, but before folding
the result into the full partial-converse package.
-/
structure ProjectiveAtlasConstructionPackage (x₀ : X) (g : HyperbolicMetric X) where
  /-- The projectivized analytic package feeding the atlas construction. -/
  projectivizedAnalyticPackage : g.AdmitsProjectivizedAnalyticPackage x₀
  /-- The projective atlas built from the curvature-aware developing pipeline. -/
  projectiveAtlasPipeline : g.AdmitsProjectiveAtlasForDevelopingCurvaturePipeline x₀
  /-- The curvature-aware projectivized developing pipeline. -/
  curvatureProjectivizedPipeline :
    g.AdmitsCurvatureProjectivizedDevelopingPipeline x₀
  /-- The induced complex projective structure with real holonomy. -/
  inducedRealProjectiveStructure : g.InducesRealProjectiveStructure x₀

/-- Prop-level target for the projective-atlas construction output package. -/
def AdmitsProjectiveAtlasConstructionPackage
    (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (g.ProjectiveAtlasConstructionPackage x₀)

/--
The assembled output of the partial converse:

from curvature `-1` local formulas, through analytic continuation and the
projective-atlas construction, to a real-holonomy projective structure.
-/
structure PartialConversePackage (x₀ : X) (g : HyperbolicMetric X) where
  /-- The local curvature-solving package. -/
  localSolvingPackage : g.AdmitsCurvatureLocalSolvingPackage
  /-- Curvature-derived Liouville formula charts. -/
  curvatureFormulaAtlas : g.HasCurvatureLiouvilleFormulaAtlas
  /-- Coordinate Poincare pullback formula charts. -/
  coordinatePullbackFormulaAtlas : g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas
  /-- Local maps to the upper half-plane whose pullback metric is `g`. -/
  upperHalfPlaneLocalModels : g.HasUpperHalfPlaneLocalModels
  /-- The curvature-aware developing pipeline. -/
  developingCurvaturePipeline : g.HasDevelopingCurvaturePipeline x₀
  /-- The analytic hyperbolic output package before projectivization. -/
  analyticPackage : g.AdmitsHyperbolicDevelopingAnalyticPackage x₀
  /-- The projectivized analytic package before constructing the atlas on `X`. -/
  projectivizedAnalyticPackage : g.AdmitsProjectivizedAnalyticPackage x₀
  /-- The projective-atlas construction output package. -/
  projectiveAtlasConstructionPackage :
    g.AdmitsProjectiveAtlasConstructionPackage x₀
  /-- A lifted developing map with `SL(2, ℝ)` holonomy. -/
  liftedDevelopingMap : g.AdmitsLiftedDevelopingMap x₀
  /-- The ordinary developing map with `PSL(2, ℝ)` holonomy. -/
  developingMap : g.AdmitsDevelopingMap x₀
  /-- The projectivized developing map to the Riemann sphere. -/
  projectivizedDevelopingMap : g.AdmitsProjectivizedDevelopingMap x₀
  /-- The projective atlas built from the curvature-aware developing pipeline. -/
  projectiveAtlasPipeline : g.AdmitsProjectiveAtlasForDevelopingCurvaturePipeline x₀
  /-- The curvature-aware projectivized developing pipeline. -/
  curvatureProjectivizedPipeline :
    g.AdmitsCurvatureProjectivizedDevelopingPipeline x₀
  /-- The induced complex projective structure with real holonomy. -/
  inducedRealProjectiveStructure : g.InducesRealProjectiveStructure x₀

/-- Prop-level target for the assembled partial converse package. -/
def AdmitsPartialConversePackage (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (g.PartialConversePackage x₀)

namespace HyperbolicDevelopingAnalyticData

variable {x₀ : X} {g : HyperbolicMetric X}

/-- Assemble the curvature-aware developing pipeline from analytic data. -/
def toHyperbolicDevelopingCurvaturePipeline
    (D : g.HyperbolicDevelopingAnalyticData x₀) :
    HyperbolicDevelopingCurvaturePipeline X x₀ g where
  localCurvatureConstructions := D.localCurvatureConstructions
  continuationData := D.continuationData
  continuation_uses_curvature_constructions :=
    D.continuation_uses_curvature_constructions

end HyperbolicDevelopingAnalyticData

theorem hasDevelopingCurvaturePipeline_of_hasHyperbolicDevelopingAnalyticData
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasHyperbolicDevelopingAnalyticData x₀) :
    g.HasDevelopingCurvaturePipeline x₀ :=
  h.elim fun D ↦ ⟨D.toHyperbolicDevelopingCurvaturePipeline⟩

theorem admitsCurvatureLocalSolvingPackage_of_hasHyperbolicDevelopingAnalyticData
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasHyperbolicDevelopingAnalyticData x₀) :
    g.AdmitsCurvatureLocalSolvingPackage :=
  h.elim fun D ↦ D.localSolvingPackage

theorem admitsLiftedDevelopingMap_of_hasHyperbolicDevelopingAnalyticData
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasHyperbolicDevelopingAnalyticData x₀) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  admitsLiftedDevelopingMap_of_hasDevelopingCurvaturePipeline
    (hasDevelopingCurvaturePipeline_of_hasHyperbolicDevelopingAnalyticData h)

theorem admitsDevelopingMap_of_hasHyperbolicDevelopingAnalyticData
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasHyperbolicDevelopingAnalyticData x₀) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_hasDevelopingCurvaturePipeline
    (hasDevelopingCurvaturePipeline_of_hasHyperbolicDevelopingAnalyticData h)

theorem hasUpperHalfPlaneLocalModels_of_hasHyperbolicDevelopingAnalyticData
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasHyperbolicDevelopingAnalyticData x₀) :
    g.HasUpperHalfPlaneLocalModels :=
  hasUpperHalfPlaneLocalModels_of_hasDevelopingCurvaturePipeline
    (hasDevelopingCurvaturePipeline_of_hasHyperbolicDevelopingAnalyticData h)

/-- Assemble the analytic output package from the analytic input data. -/
def hyperbolicDevelopingAnalyticPackage_of_hasHyperbolicDevelopingAnalyticData
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasHyperbolicDevelopingAnalyticData x₀) :
    g.HyperbolicDevelopingAnalyticPackage x₀ where
  localSolvingPackage :=
    h.elim fun D ↦ D.localSolvingPackage
  curvatureFormulaAtlas :=
    hasCurvatureLiouvilleFormulaAtlas_of_hasDevelopingCurvaturePipeline
      (hasDevelopingCurvaturePipeline_of_hasHyperbolicDevelopingAnalyticData h)
  coordinatePullbackFormulaAtlas :=
    hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasDevelopingCurvaturePipeline
      (hasDevelopingCurvaturePipeline_of_hasHyperbolicDevelopingAnalyticData h)
  upperHalfPlaneLocalModels :=
    hasUpperHalfPlaneLocalModels_of_hasHyperbolicDevelopingAnalyticData h
  developingCurvaturePipeline :=
    hasDevelopingCurvaturePipeline_of_hasHyperbolicDevelopingAnalyticData h
  liftedDevelopingMap :=
    admitsLiftedDevelopingMap_of_hasHyperbolicDevelopingAnalyticData h
  developingMap :=
    admitsDevelopingMap_of_hasHyperbolicDevelopingAnalyticData h

theorem admitsHyperbolicDevelopingAnalyticPackage_of_hasHyperbolicDevelopingAnalyticData
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasHyperbolicDevelopingAnalyticData x₀) :
    g.AdmitsHyperbolicDevelopingAnalyticPackage x₀ :=
  ⟨hyperbolicDevelopingAnalyticPackage_of_hasHyperbolicDevelopingAnalyticData h⟩

/-- Forget projective data and keep the analytic input data underlying a curvature pipeline. -/
def hyperbolicDevelopingAnalyticData_of_hyperbolicDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (P : HyperbolicDevelopingCurvaturePipeline X x₀ g) :
    g.HyperbolicDevelopingAnalyticData x₀ where
  localSolvingPackage :=
    admitsCurvatureLocalSolvingPackage_of_hasCurvatureLiouvilleDevelopingConstructionAtlas
      P.localCurvatureConstructions
  localCurvatureConstructions := P.localCurvatureConstructions
  continuationData := P.continuationData
  continuation_uses_curvature_constructions :=
    P.continuation_uses_curvature_constructions

theorem hasHyperbolicDevelopingAnalyticData_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.HasHyperbolicDevelopingAnalyticData x₀ :=
  h.elim fun P ↦
    ⟨hyperbolicDevelopingAnalyticData_of_hyperbolicDevelopingCurvaturePipeline P⟩

theorem admitsHyperbolicDevelopingAnalyticPackage_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.AdmitsHyperbolicDevelopingAnalyticPackage x₀ :=
  admitsHyperbolicDevelopingAnalyticPackage_of_hasHyperbolicDevelopingAnalyticData
    (hasHyperbolicDevelopingAnalyticData_of_hasDevelopingCurvaturePipeline h)

theorem admitsDevelopingMap_of_admitsHyperbolicDevelopingAnalyticPackage
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsHyperbolicDevelopingAnalyticPackage x₀) :
    g.AdmitsDevelopingMap x₀ :=
  h.elim fun H ↦ H.developingMap

theorem admitsCurvatureLocalSolvingPackage_of_admitsHyperbolicDevelopingAnalyticPackage
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsHyperbolicDevelopingAnalyticPackage x₀) :
    g.AdmitsCurvatureLocalSolvingPackage :=
  h.elim fun H ↦ H.localSolvingPackage

theorem hasUpperHalfPlaneLocalModels_of_admitsHyperbolicDevelopingAnalyticPackage
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsHyperbolicDevelopingAnalyticPackage x₀) :
    g.HasUpperHalfPlaneLocalModels :=
  h.elim fun H ↦ H.upperHalfPlaneLocalModels

theorem admitsProjectivizedDevelopingMap_of_hasHyperbolicDevelopingAnalyticData
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasHyperbolicDevelopingAnalyticData x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  admitsProjectivizedDevelopingMap_of_hasDevelopingCurvaturePipeline
    (hasDevelopingCurvaturePipeline_of_hasHyperbolicDevelopingAnalyticData h)

theorem admitsProjectivizedDevelopingMap_of_admitsHyperbolicDevelopingAnalyticPackage
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsHyperbolicDevelopingAnalyticPackage x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  h.elim fun H ↦
    admitsProjectivizedDevelopingMap_of_hasDevelopingCurvaturePipeline
      H.developingCurvaturePipeline

def projectivizedAnalyticPackage_of_hasHyperbolicDevelopingAnalyticData
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasHyperbolicDevelopingAnalyticData x₀) :
    g.ProjectivizedAnalyticPackage x₀ where
  analyticPackage :=
    admitsHyperbolicDevelopingAnalyticPackage_of_hasHyperbolicDevelopingAnalyticData h
  projectivizedDevelopingMap :=
    admitsProjectivizedDevelopingMap_of_hasHyperbolicDevelopingAnalyticData h

theorem admitsProjectivizedAnalyticPackage_of_hasHyperbolicDevelopingAnalyticData
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasHyperbolicDevelopingAnalyticData x₀) :
    g.AdmitsProjectivizedAnalyticPackage x₀ :=
  ⟨projectivizedAnalyticPackage_of_hasHyperbolicDevelopingAnalyticData h⟩

theorem admitsProjectivizedAnalyticPackage_of_hasDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingCurvaturePipeline x₀) :
    g.AdmitsProjectivizedAnalyticPackage x₀ :=
  admitsProjectivizedAnalyticPackage_of_hasHyperbolicDevelopingAnalyticData
    (hasHyperbolicDevelopingAnalyticData_of_hasDevelopingCurvaturePipeline h)

def projectivizedAnalyticPackage_of_admitsHyperbolicDevelopingAnalyticPackage
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsHyperbolicDevelopingAnalyticPackage x₀) :
    g.ProjectivizedAnalyticPackage x₀ where
  analyticPackage := h
  projectivizedDevelopingMap :=
    admitsProjectivizedDevelopingMap_of_admitsHyperbolicDevelopingAnalyticPackage h

theorem admitsProjectivizedAnalyticPackage_of_admitsHyperbolicDevelopingAnalyticPackage
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsHyperbolicDevelopingAnalyticPackage x₀) :
    g.AdmitsProjectivizedAnalyticPackage x₀ :=
  ⟨projectivizedAnalyticPackage_of_admitsHyperbolicDevelopingAnalyticPackage h⟩

theorem admitsProjectivizedDevelopingMap_of_admitsProjectivizedAnalyticPackage
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectivizedAnalyticPackage x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  h.elim fun H ↦ H.projectivizedDevelopingMap

/-- Assemble the projective-atlas construction package from the atlas pipeline. -/
def projectiveAtlasConstructionPackage_of_hasProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.ProjectiveAtlasConstructionPackage x₀ where
  projectivizedAnalyticPackage :=
    admitsProjectivizedAnalyticPackage_of_hasDevelopingCurvaturePipeline
      (hasDevelopingCurvaturePipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline h)
  projectiveAtlasPipeline :=
    admitsProjectiveAtlasForDevelopingCurvaturePipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline h
  curvatureProjectivizedPipeline :=
    admitsCurvatureProjectivizedDevelopingPipeline_of_hasCurvatureProjectivizedDevelopingPipeline
      (hasCurvatureProjectivizedDevelopingPipeline_of_hasProjectiveAtlasForDevelopingCurvaturePipeline h)
  inducedRealProjectiveStructure :=
    inducesRealProjectiveStructure_of_hasProjectiveAtlasForDevelopingCurvaturePipeline h

theorem admitsProjectiveAtlasConstructionPackage_of_hasProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.AdmitsProjectiveAtlasConstructionPackage x₀ :=
  ⟨projectiveAtlasConstructionPackage_of_hasProjectiveAtlasForDevelopingCurvaturePipeline h⟩

theorem admitsProjectiveAtlasConstructionPackage_of_admitsProjectiveAtlasForDevelopingCurvaturePipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasForDevelopingCurvaturePipeline x₀) :
    g.AdmitsProjectiveAtlasConstructionPackage x₀ :=
  h.elim fun H ↦
    admitsProjectiveAtlasConstructionPackage_of_hasProjectiveAtlasForDevelopingCurvaturePipeline H

theorem inducesRealProjectiveStructure_of_admitsProjectiveAtlasConstructionPackage
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasConstructionPackage x₀) :
    g.InducesRealProjectiveStructure x₀ :=
  h.elim fun H ↦ H.inducedRealProjectiveStructure

theorem admitsProjectivizedAnalyticPackage_of_admitsProjectiveAtlasConstructionPackage
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasConstructionPackage x₀) :
    g.AdmitsProjectivizedAnalyticPackage x₀ :=
  h.elim fun H ↦ H.projectivizedAnalyticPackage

theorem admitsProjectivizedDevelopingMap_of_admitsProjectiveAtlasConstructionPackage
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasConstructionPackage x₀) :
    g.AdmitsProjectivizedDevelopingMap x₀ :=
  admitsProjectivizedDevelopingMap_of_admitsProjectivizedAnalyticPackage
    (admitsProjectivizedAnalyticPackage_of_admitsProjectiveAtlasConstructionPackage h)

theorem admitsProjectiveAtlasForDevelopingCurvaturePipeline_of_admitsProjectiveAtlasConstructionPackage
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasConstructionPackage x₀) :
    g.AdmitsProjectiveAtlasForDevelopingCurvaturePipeline x₀ :=
  h.elim fun H ↦ H.projectiveAtlasPipeline

theorem admitsCurvatureProjectivizedDevelopingPipeline_of_admitsProjectiveAtlasConstructionPackage
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.AdmitsProjectiveAtlasConstructionPackage x₀) :
    g.AdmitsCurvatureProjectivizedDevelopingPipeline x₀ :=
  h.elim fun H ↦ H.curvatureProjectivizedPipeline

/--
Input data for the partial converse, split along the intended proof:

1. solve the curvature-derived local Liouville problem;
2. analytically continue the resulting local models;
3. build the projective atlas from the projectivized developing map.
-/
structure PartialConverseConstructionData (x₀ : X) (g : HyperbolicMetric X) where
  /-- Curvature-derived local formulas solved by maps to `ℍ`. -/
  localCurvatureConstructions : g.HasCurvatureLiouvilleDevelopingConstructionAtlas
  /-- Analytic continuation of the local models on the simply connected cover. -/
  continuationData : HyperbolicDevelopingContinuationData X x₀ g
  /-- The continuation data uses the local models obtained from the local constructions. -/
  continuation_uses_curvature_constructions :
    continuationData.localModels =
      (LocalLiouvilleDevelopingConstructionAtlas.toLocalLiouvilleDevelopingSolutionAtlas
        localCurvatureConstructions.developingConstructionAtlas).toHyperbolicLocalModelAtlas
  /-- The projective atlas built from the projectivized developing map produced above. -/
  atlasFromDevelopingMap :
    ProjectiveAtlasFromDevelopingMap X
      (({
        localCurvatureConstructions := localCurvatureConstructions
        continuationData := continuationData
        continuation_uses_curvature_constructions :=
          continuation_uses_curvature_constructions
      } : HyperbolicDevelopingCurvaturePipeline X x₀ g).toProjectivizedDevelopingMap)

/-- Prop-level target for the input side of the partial converse proof. -/
def HasPartialConverseConstructionData (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (g.PartialConverseConstructionData x₀)

/--
Global construction theorem target for a Riemann surface.

It says that every hyperbolic metric admits the decomposed construction data:
local curvature solving, analytic continuation, and the projective atlas built
from the projectivized developing map.
-/
def PartialConverseConstructionTheorem (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X), g.HasPartialConverseConstructionData x₀

/--
Global partial-converse theorem target for a Riemann surface.

For every basepoint and every hyperbolic metric, the full partial-converse
package is available.  This is a theorem target, not a theorem currently
derived from the boundary-input packages.
-/
def PartialConverseTheorem (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X), g.AdmitsPartialConversePackage x₀

/--
Global theorem target retaining only the three main outputs of the partial
converse.  Conditional assembly lemmas may produce this from explicit theorem
packages, but those lemmas should keep their assumptions in their names.
-/
def PartialConverseMainOutputsTheorem (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    g.AdmitsDevelopingMap x₀ ∧
      g.AdmitsProjectivizedDevelopingMap x₀ ∧
        g.InducesRealProjectiveStructure x₀

/--
%%handwave
name:
  Complete partial converse theorem shape
statement:
  The endpoint proposition states that every hyperbolic metric on a connected
  Riemann surface induces a complex projective structure, and that the
  resulting projective holonomy is certified to factor through
  $\mathrm{PSL}_2(\mathbb R)$.
  The basepoint appears only as an existential witness for the holonomy
  certificate.
-/
def CompletePartialConverseTheorem (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] : Prop :=
  ∀ g : HyperbolicMetric X,
    ∃ P : ComplexProjectiveStructure X,
      P.IsInducedByHyperbolicMetric g ∧
        ∃ x₀ : X, HasPSL2RHolonomy x₀ P

/--
The older three-output package implies the explicit projective-structure
converse statement.
-/
theorem complete_partial_converse_theorem_of_partial_converse_main_outputs_theorem
    (h : PartialConverseMainOutputsTheorem X) :
    CompletePartialConverseTheorem X := by
  intro g
  let x₀ : X := Classical.choice inferInstance
  rcases (h x₀ g).2.2 with ⟨P⟩
  exact
    ⟨P.projectiveStructure,
      ComplexProjectiveStructure.isInducedByHyperbolicMetric_of_hyperbolic_induced_projective_structure P,
      x₀, P.hasPSL2RHolonomy⟩

/--
Continuation data constructed from a fixed curvature-derived local solving
atlas.
-/
structure ContinuationFromCurvatureLocalConstructions
    (x₀ : X) (g : HyperbolicMetric X)
    (localCurvatureConstructions :
      g.HasCurvatureLiouvilleDevelopingConstructionAtlas) where
  /-- Analytic continuation of the corresponding local models. -/
  continuationData : HyperbolicDevelopingContinuationData X x₀ g
  /-- The continuation data uses the local models selected by the local solving atlas. -/
  continuation_uses_curvature_constructions :
    continuationData.localModels =
      (LocalLiouvilleDevelopingConstructionAtlas.toLocalLiouvilleDevelopingSolutionAtlas
        localCurvatureConstructions.developingConstructionAtlas).toHyperbolicLocalModelAtlas

end HyperbolicMetric

end

end JJMath
