import JJMath.Hyperbolic.Converse.Continuation.LegacyAnalyticContinuation

/-!
# Split analytic continuation targets for the partial converse
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/--
Path-homotopy-class analytic-continuation theorem for arbitrary local model
atlases.
-/
def AnalyticContinuationPathClassContinuationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g),
    Nonempty (PathClassAnalyticContinuationData x₀ g localModels)

/--
Loop-equivariance theorem for arbitrary path-class continuation data.
-/
def AnalyticContinuationPathClassEquivarianceTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g)
    (pathClassContinuation :
      PathClassAnalyticContinuationData x₀ g localModels),
    Nonempty
      (PathClassAnalyticContinuationEquivarianceData
        pathClassContinuation)

/--
Path-homotopy-class analytic-continuation theorem for arbitrary local model
atlases.
-/
def AnalyticContinuationPathClassMonodromyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g),
    Nonempty (PathClassAnalyticContinuationMonodromyData x₀ g localModels)

/--
Path-class continuation plus loop equivariance give path-class monodromy.
-/
def analyticContinuationPathClassMonodromyTheorem_of_pathClassContinuation_and_pathClassEquivariance
    (hContinuation :
      AnalyticContinuationPathClassContinuationTheorem X)
    (hEquivariance :
      AnalyticContinuationPathClassEquivarianceTheorem X) :
    AnalyticContinuationPathClassMonodromyTheorem X := by
  intro x₀ g localModels
  rcases hContinuation x₀ g localModels with ⟨C⟩
  rcases hEquivariance x₀ g localModels C with ⟨E⟩
  exact
    ⟨E.toPathClassAnalyticContinuationMonodromyData⟩

/--
Representative-path analytic-continuation theorem for arbitrary local model
atlases.
-/
def AnalyticContinuationPathContinuationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g),
    Nonempty (PathAnalyticContinuationData x₀ g localModels)

/--
Loop-equivariance theorem for arbitrary representative-path continuation data.
-/
def AnalyticContinuationPathEquivarianceTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g)
    (pathContinuation :
      PathAnalyticContinuationData x₀ g localModels),
    Nonempty
      (PathAnalyticContinuationEquivarianceData
        pathContinuation)

/--
Representative-path analytic-continuation theorem for arbitrary local model
atlases.
-/
def AnalyticContinuationPathMonodromyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g),
    Nonempty (PathAnalyticContinuationMonodromyData x₀ g localModels)

/--
Representative-path continuation plus loop equivariance give
representative-path monodromy.
-/
def analyticContinuationPathMonodromyTheorem_of_pathContinuation_and_pathEquivariance
    (hContinuation :
      AnalyticContinuationPathContinuationTheorem X)
    (hEquivariance :
      AnalyticContinuationPathEquivarianceTheorem X) :
    AnalyticContinuationPathMonodromyTheorem X := by
  intro x₀ g localModels
  rcases hContinuation x₀ g localModels with ⟨C⟩
  rcases hEquivariance x₀ g localModels C with ⟨E⟩
  exact
    ⟨E.toPathAnalyticContinuationMonodromyData⟩

/--
Terminal-branch representative-path analytic-continuation theorem for
arbitrary local model atlases.
-/
def AnalyticContinuationPathTerminalBranchMonodromyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g),
    Nonempty
      (PathTerminalBranchAnalyticContinuationMonodromyData
        x₀ g localModels)

/--
Finite-chain terminal-branch representative-path analytic-continuation theorem
for arbitrary local model atlases.
-/
def AnalyticContinuationPathChainTerminalBranchMonodromyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g),
    Nonempty
      (PathChainTerminalBranchAnalyticContinuationMonodromyData
        x₀ g localModels)

/--
Finite-chain terminal-branch representative-path analytic-continuation theorem
for arbitrary local model atlases, with only value-level homotopy descent of
terminal branches.
-/
def AnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g),
    Nonempty
      (PathChainTerminalBranchAnalyticContinuationValueMonodromyData
        x₀ g localModels)

/--
Finite-chain terminal-branch value-continuation theorem for arbitrary local
model atlases, before loop monodromy/equivariance is imposed.
-/
def AnalyticContinuationPathChainTerminalBranchValueContinuationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g),
    Nonempty
      (PathChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels)

/--
Loop-equivariance theorem for arbitrary value-level finite-chain terminal
continuation data.
-/
def AnalyticContinuationPathChainTerminalBranchValueEquivarianceTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g)
    (chainTerminalContinuation :
      PathChainTerminalBranchAnalyticContinuationValueData x₀ g localModels),
    Nonempty
      (PathChainTerminalBranchAnalyticContinuationValueEquivarianceData
        chainTerminalContinuation)

/--
Value-continuation plus loop equivariance give value-level finite-chain
terminal-branch monodromy.
-/
def analyticContinuationPathChainTerminalBranchValueMonodromyTheorem_of_valueContinuation_and_valueEquivariance
    (hContinuation :
      AnalyticContinuationPathChainTerminalBranchValueContinuationTheorem X)
    (hEquivariance :
      AnalyticContinuationPathChainTerminalBranchValueEquivarianceTheorem X) :
    AnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem X := by
  intro x₀ g localModels
  rcases hContinuation x₀ g localModels with ⟨C⟩
  rcases hEquivariance x₀ g localModels C with ⟨E⟩
  exact
    ⟨E.toPathChainTerminalBranchAnalyticContinuationValueMonodromyData⟩

/--
Finite-chain terminal-branch monodromy data imply terminal-branch monodromy
data.
-/
def analyticContinuationPathTerminalBranchMonodromyTheorem_of_pathChainTerminalBranchMonodromyTheorem
    (h : AnalyticContinuationPathChainTerminalBranchMonodromyTheorem X) :
    AnalyticContinuationPathTerminalBranchMonodromyTheorem X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    PathChainTerminalBranchAnalyticContinuationMonodromyData.toPathTerminalBranchAnalyticContinuationMonodromyData

/--
Strong finite-chain terminal-branch monodromy data imply the weaker
value-level finite-chain monodromy boundary.
-/
def analyticContinuationPathChainTerminalBranchValueMonodromyTheorem_of_pathChainTerminalBranchMonodromyTheorem
    (h : AnalyticContinuationPathChainTerminalBranchMonodromyTheorem X) :
    AnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    PathChainTerminalBranchAnalyticContinuationMonodromyData.toPathChainTerminalBranchAnalyticContinuationValueMonodromyData

/--
Terminal-branch monodromy data imply the representative-path monodromy
boundary.
-/
def analyticContinuationPathMonodromyTheorem_of_pathTerminalBranchMonodromyTheorem
    (h : AnalyticContinuationPathTerminalBranchMonodromyTheorem X) :
    AnalyticContinuationPathMonodromyTheorem X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    PathTerminalBranchAnalyticContinuationMonodromyData.toPathAnalyticContinuationMonodromyData

/--
Representative-path monodromy data imply the path-homotopy-class monodromy
boundary.
-/
def analyticContinuationPathClassMonodromyTheorem_of_pathMonodromyTheorem
    (h : AnalyticContinuationPathMonodromyTheorem X) :
    AnalyticContinuationPathClassMonodromyTheorem X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    PathAnalyticContinuationMonodromyData.toPathClassAnalyticContinuationMonodromyData

/--
Terminal-branch monodromy data imply the path-homotopy-class monodromy
boundary.
-/
def analyticContinuationPathClassMonodromyTheorem_of_pathTerminalBranchMonodromyTheorem
    (h : AnalyticContinuationPathTerminalBranchMonodromyTheorem X) :
    AnalyticContinuationPathClassMonodromyTheorem X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    PathTerminalBranchAnalyticContinuationMonodromyData.toPathClassAnalyticContinuationMonodromyData

/--
Finite-chain terminal-branch monodromy data imply the path-homotopy-class
monodromy boundary.
-/
def analyticContinuationPathClassMonodromyTheorem_of_pathChainTerminalBranchMonodromyTheorem
    (h : AnalyticContinuationPathChainTerminalBranchMonodromyTheorem X) :
    AnalyticContinuationPathClassMonodromyTheorem X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    PathChainTerminalBranchAnalyticContinuationMonodromyData.toPathClassAnalyticContinuationMonodromyData

/--
Value-level finite-chain terminal-branch monodromy data imply the
path-homotopy-class monodromy boundary.
-/
noncomputable def analyticContinuationPathClassMonodromyTheorem_of_pathChainTerminalBranchValueMonodromyTheorem
    (h : AnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem X) :
    AnalyticContinuationPathClassMonodromyTheorem X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    PathChainTerminalBranchAnalyticContinuationValueMonodromyData.toPathClassAnalyticContinuationMonodromyData

/--
Finite-chain terminal-branch monodromy data imply the representative-path
monodromy boundary.
-/
def analyticContinuationPathMonodromyTheorem_of_pathChainTerminalBranchMonodromyTheorem
    (h : AnalyticContinuationPathChainTerminalBranchMonodromyTheorem X) :
    AnalyticContinuationPathMonodromyTheorem X :=
  analyticContinuationPathMonodromyTheorem_of_pathTerminalBranchMonodromyTheorem
    (analyticContinuationPathTerminalBranchMonodromyTheorem_of_pathChainTerminalBranchMonodromyTheorem
      h)

/--
The true analytic-continuation/monodromy boundary for arbitrary local model
atlases: construct the sheetwise continuation data on the canonical cover and
prove the resulting real Mobius deck equivariance.
-/
def AnalyticContinuationMonodromyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g),
    Nonempty (AnalyticContinuationMonodromyData x₀ g localModels)

/--
The true analytic-continuation/monodromy boundary for arbitrary
local-transition atlases: construct sheetwise continuation data on the
canonical cover and prove real Mobius deck equivariance.
-/
def AnalyticContinuationFromLocalTransitionModelsMonodromyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g),
    Nonempty
      (LocalTransitionAnalyticContinuationMonodromyData
        x₀ g localModels)

/--
Path-class monodromy data imply the cover-level analytic-continuation
monodromy boundary.
-/
def analyticContinuationMonodromyTheorem_of_pathClassMonodromyTheorem
    (h : AnalyticContinuationPathClassMonodromyTheorem X) :
    AnalyticContinuationMonodromyTheorem X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    PathClassAnalyticContinuationMonodromyData.toAnalyticContinuationMonodromyData

/--
Representative-path monodromy data imply the cover-level
analytic-continuation monodromy boundary.
-/
def analyticContinuationMonodromyTheorem_of_pathMonodromyTheorem
    (h : AnalyticContinuationPathMonodromyTheorem X) :
    AnalyticContinuationMonodromyTheorem X :=
  analyticContinuationMonodromyTheorem_of_pathClassMonodromyTheorem
    (analyticContinuationPathClassMonodromyTheorem_of_pathMonodromyTheorem h)

/--
Terminal-branch monodromy data imply the cover-level analytic-continuation
monodromy boundary.
-/
def analyticContinuationMonodromyTheorem_of_pathTerminalBranchMonodromyTheorem
    (h : AnalyticContinuationPathTerminalBranchMonodromyTheorem X) :
    AnalyticContinuationMonodromyTheorem X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    PathTerminalBranchAnalyticContinuationMonodromyData.toAnalyticContinuationMonodromyData

/--
Finite-chain terminal-branch monodromy data imply the cover-level
analytic-continuation monodromy boundary.
-/
def analyticContinuationMonodromyTheorem_of_pathChainTerminalBranchMonodromyTheorem
    (h : AnalyticContinuationPathChainTerminalBranchMonodromyTheorem X) :
    AnalyticContinuationMonodromyTheorem X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    PathChainTerminalBranchAnalyticContinuationMonodromyData.toAnalyticContinuationMonodromyData

/--
Value-level finite-chain terminal-branch monodromy data imply the cover-level
analytic-continuation monodromy boundary.
-/
noncomputable def analyticContinuationMonodromyTheorem_of_pathChainTerminalBranchValueMonodromyTheorem
    (h : AnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem X) :
    AnalyticContinuationMonodromyTheorem X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    PathChainTerminalBranchAnalyticContinuationValueMonodromyData.toAnalyticContinuationMonodromyData

/--
Reduced analytic-continuation theorem after the canonical cover, canonical
pulled-back metric, and all developing-map regularity have been discharged.

The remaining fields are the actual continuation/monodromy data: the continued
map, the lifted real holonomy, equivariance, and local agreement with the
chosen local models.  The pullback metric identity is derived from local-model
agreement.
-/
def AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g),
    Nonempty
      (HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels)

/--
The monodromy boundary implies the reduced continuation-field theorem by
deriving regularity and the metric pullback from the explicit local branch
formulas.
-/
def analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem_of_monodromyTheorem
    (h : AnalyticContinuationMonodromyTheorem X) :
    AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    AnalyticContinuationMonodromyData.toDerivedRegularityFields

/--
The path-class monodromy theorem also implies the reduced
continuation-field theorem.
-/
def analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem_of_pathClassMonodromyTheorem
    (h : AnalyticContinuationPathClassMonodromyTheorem X) :
    AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X :=
  analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem_of_monodromyTheorem
    (analyticContinuationMonodromyTheorem_of_pathClassMonodromyTheorem h)

/--
The representative-path monodromy theorem also implies the reduced
continuation-field theorem.
-/
def analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem_of_pathMonodromyTheorem
    (h : AnalyticContinuationPathMonodromyTheorem X) :
    AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X :=
  analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem_of_pathClassMonodromyTheorem
    (analyticContinuationPathClassMonodromyTheorem_of_pathMonodromyTheorem h)

/--
The terminal-branch monodromy theorem also implies the reduced
continuation-field theorem.
-/
def analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem_of_pathTerminalBranchMonodromyTheorem
    (h : AnalyticContinuationPathTerminalBranchMonodromyTheorem X) :
    AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X :=
  analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem_of_monodromyTheorem
    (analyticContinuationMonodromyTheorem_of_pathTerminalBranchMonodromyTheorem h)

/--
The finite-chain terminal-branch monodromy theorem also implies the reduced
continuation-field theorem.
-/
def analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem_of_pathChainTerminalBranchMonodromyTheorem
    (h : AnalyticContinuationPathChainTerminalBranchMonodromyTheorem X) :
    AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X :=
  analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem_of_pathClassMonodromyTheorem
    (analyticContinuationPathClassMonodromyTheorem_of_pathChainTerminalBranchMonodromyTheorem
      h)

/--
The value-level finite-chain terminal-branch monodromy theorem also implies
the reduced continuation-field theorem.
-/
noncomputable def analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem_of_pathChainTerminalBranchValueMonodromyTheorem
    (h : AnalyticContinuationPathChainTerminalBranchValueMonodromyTheorem X) :
    AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X :=
  analyticContinuationFromLocalModelsDerivedRegularityFieldTheorem_of_pathClassMonodromyTheorem
    (analyticContinuationPathClassMonodromyTheorem_of_pathChainTerminalBranchValueMonodromyTheorem
      h)

/--
Analytic-continuation theorem stated as explicit continuation fields for every
local model atlas.
-/
def AnalyticContinuationFromLocalModelsFieldTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g),
    Nonempty (HyperbolicDevelopingContinuationDataFields x₀ g localModels)

/--
Analytic-continuation theorem stated for local-transition local model atlases.

This is the componentwise-overlap version of the continuation boundary: the
input atlas is only required to have real-Mobius representatives locally on
overlaps.
-/
def AnalyticContinuationFromLocalTransitionModelsFieldTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g),
    Nonempty
      (HyperbolicDevelopingLocalTransitionContinuationDataFields
        x₀ g localModels)

/--
Analytic-continuation theorem for local-transition atlases with the canonical
cover and canonical pulled-back metric already fixed.
-/
def AnalyticContinuationFromLocalTransitionModelsCanonicalCoverMetricFieldTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g),
    Nonempty
      (HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric
        x₀ g localModels)

/--
Analytic-continuation theorem for local-transition atlases with regularity and
metric recovery derived from local agreement on the canonical cover.
-/
def AnalyticContinuationFromLocalTransitionModelsDerivedRegularityCanonicalCoverMetricFieldTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g),
    Nonempty
      (HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g localModels)

/--
The local-transition monodromy boundary implies the reduced local-transition
continuation-field theorem by deriving regularity and metric recovery from the
explicit sheetwise branch formulas.
-/
def analyticContinuationFromLocalTransitionModelsDerivedRegularityCanonicalCoverMetricFieldTheorem_of_monodromyTheorem
    (h : AnalyticContinuationFromLocalTransitionModelsMonodromyTheorem X) :
    AnalyticContinuationFromLocalTransitionModelsDerivedRegularityCanonicalCoverMetricFieldTheorem
      X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    LocalTransitionAnalyticContinuationMonodromyData.toDerivedRegularityFields

/--
The canonical-cover local-transition continuation boundary implies the
ordinary local-transition continuation field theorem.
-/
def analyticContinuationFromLocalTransitionModelsFieldTheorem_of_canonicalCoverMetricFieldTheorem
    (h :
      AnalyticContinuationFromLocalTransitionModelsCanonicalCoverMetricFieldTheorem
        X) :
    AnalyticContinuationFromLocalTransitionModelsFieldTheorem X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric.toHyperbolicDevelopingLocalTransitionContinuationDataFields

/--
The derived-regularity local-transition continuation boundary implies the
canonical-cover local-transition field theorem.
-/
def analyticContinuationFromLocalTransitionModelsCanonicalCoverMetricFieldTheorem_of_derivedRegularityCanonicalCoverMetricFieldTheorem
    (h :
      AnalyticContinuationFromLocalTransitionModelsDerivedRegularityCanonicalCoverMetricFieldTheorem
        X) :
    AnalyticContinuationFromLocalTransitionModelsCanonicalCoverMetricFieldTheorem
      X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity.toHyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric

/--
The derived-regularity local-transition continuation boundary also implies
the ordinary local-transition field theorem.
-/
def analyticContinuationFromLocalTransitionModelsFieldTheorem_of_derivedRegularityCanonicalCoverMetricFieldTheorem
    (h :
      AnalyticContinuationFromLocalTransitionModelsDerivedRegularityCanonicalCoverMetricFieldTheorem
        X) :
    AnalyticContinuationFromLocalTransitionModelsFieldTheorem X :=
  analyticContinuationFromLocalTransitionModelsFieldTheorem_of_canonicalCoverMetricFieldTheorem
    (analyticContinuationFromLocalTransitionModelsCanonicalCoverMetricFieldTheorem_of_derivedRegularityCanonicalCoverMetricFieldTheorem
      h)

/--
The reduced continuation boundary implies the original all-fields continuation
theorem, because local-model agreement derives continuity, holomorphicity,
nonzero derivative, and concrete local-biholomorphism branch data.
-/
def analyticContinuationFromLocalModelsFieldTheorem_of_derivedRegularityFieldTheorem
    (h : AnalyticContinuationFromLocalModelsDerivedRegularityFieldTheorem X) :
    AnalyticContinuationFromLocalModelsFieldTheorem X := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    HyperbolicDevelopingContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity.toHyperbolicDevelopingContinuationDataFields

/--
The old global-overlap field theorem gives the local-transition field theorem
for every atlas that actually came with global overlap representatives.
-/
@[reducible] def analyticContinuationFromLocalModelsFieldTheorem_to_localTransitionFields
    (h : AnalyticContinuationFromLocalModelsFieldTheorem X) :
    ∀ (x₀ : X) (g : HyperbolicMetric X)
      (localModels : HyperbolicLocalModelAtlas X g),
      Nonempty
        (HyperbolicDevelopingLocalTransitionContinuationDataFields
          x₀ g localModels.toLocalTransitionAtlas) := by
  intro x₀ g localModels
  exact (h x₀ g localModels).map
    HyperbolicDevelopingContinuationDataFields.toLocalTransitionFields

/--
Global theorem target for analytically continuing any chosen local
upper-half-plane model atlas.
-/
def AnalyticContinuationFromLocalModelsTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g),
    Nonempty (ContinuationFromLocalModels x₀ g localModels)

/--
Global theorem target for analytically continuing any chosen local-transition
upper-half-plane model atlas.
-/
def AnalyticContinuationFromLocalTransitionModelsTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g),
    Nonempty (ContinuationFromLocalTransitionModels x₀ g localModels)

/--
Explicit local-transition continuation fields only for a fixed selected local
model atlas.
-/
def SelectedLocalTransitionModelContinuationFieldTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (HyperbolicDevelopingLocalTransitionContinuationDataFields
        x₀ g (chosenLocalModels g))

/--
Explicit local-transition continuation fields on the canonical cover and
canonical pulled-back metric, for a fixed selected local-transition atlas.
-/
def SelectedLocalTransitionModelContinuationCanonicalCoverMetricFieldTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetric
        x₀ g (chosenLocalModels g))

/--
Reduced local-transition continuation fields on the canonical cover for a
fixed selected local-transition atlas.
-/
def SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularity
        x₀ g (chosenLocalModels g))

/--
Reduced PSL-valued local-transition continuation fields on the canonical cover
for a fixed selected local-transition atlas.
-/
def SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
        x₀ g (chosenLocalModels g))

/--
Local-transition monodromy data only for a fixed selected local-transition
atlas.
-/
def SelectedLocalTransitionModelAnalyticContinuationMonodromyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (LocalTransitionAnalyticContinuationMonodromyData
        x₀ g (chosenLocalModels g))

/--
PSL-valued path-class monodromy data only for a fixed selected
local-transition atlas.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
        x₀ g (chosenLocalModels g))

/--
PSL-valued value-level finite-chain terminal monodromy data only for a fixed
selected local-transition atlas.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathChainTerminalBranchValueMonodromyTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionChainTerminalBranchAnalyticContinuationValueMonodromyDataPSL
        x₀ g (chosenLocalModels g))

/--
Selected value-level finite-chain terminal continuation before PSL loop
monodromy/equivariance is imposed.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathChainTerminalBranchValueContinuationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
        x₀ g (chosenLocalModels g))

/--
Selected explicit handoff-chain terminal continuation before PSL loop
monodromy/equivariance is imposed.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathHandoffChainTerminalBranchValueContinuationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionHandoffChainTerminalBranchAnalyticContinuationValueData
        x₀ g (chosenLocalModels g))

/--
Selected based weak handoff terminal continuation before PSL loop
monodromy/equivariance is imposed.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalBranchValueContinuationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
        x₀ g (chosenLocalModels g))

/--
Selected based weak handoff continuation with canonical terminal sheets.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetValueContinuationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData
        x₀ g (chosenLocalModels g))

/--
Selected single-valued canonical-cover PSL continuation for based weak handoff
terminal sheets.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalCoverPSLTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
        x₀ g (chosenLocalModels g))

/--
Selected canonical-terminal-sheet agreement for based weak handoff terminal
sheets, before PSL loop monodromy/equivariance is imposed.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g))

/--
Selected terminal-sheet homotopy principle for based weak handoff skeletons.

This is the implementation-facing form of the finite homotopy-grid uniqueness
argument: it must hold for any choices of based weak handoff skeletons along
representative paths.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyPrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected coherent terminal-sheet homotopy data for based weak handoff
continuation.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyData
        x₀ g (chosenLocalModels g))

/--
Selected finite homotopy-grid walk principle for based weak handoff skeletons.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffHomotopyGridWalkPrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected elementary homotopy-grid move walk principle for based weak handoff
skeletons.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalkPrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected one-column terminal-value witness theorem for based weak handoff
skeletons.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnValueWitnessPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected decomposed one-column terminal-value witness theorem for based weak
handoff skeletons.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected exact transfer from decomposed one-column witnesses to the public
cut-path witnesses.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected explicit witness form of the cut-reparameterization boundary.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple
      x₀ g (chosenLocalModels g)

/-- Selected raw-cut explicit witness boundary. -/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnRawCutReparamExplicitValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnRawCutReparamExplicitValueWitnessPrinciple
      x₀ g (chosenLocalModels g)

/-- Selected generic subpath-merge branch-data boundary. -/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSubpathMergeBranchDataWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffSubpathMergeBranchDataWitnessPrinciple
      g (chosenLocalModels g)

/-- Selected normalized unit-split branch-data boundary. -/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffUnitSplitBranchDataWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffUnitSplitBranchDataWitnessPrinciple
      g (chosenLocalModels g)

/-- Selected interior normalized unit-split branch-data boundary. -/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffInteriorUnitSplitBranchDataWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffInteriorUnitSplitBranchDataWitnessPrinciple
      g (chosenLocalModels g)

/-- Selected generic prefixed subpath-merge value boundary. -/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffPrefixedSubpathMergeValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffPrefixedSubpathMergeValueWitnessPrinciple
      g (chosenLocalModels g)

/-- Selected monotone subpath-merge branch-data boundary. -/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessPrinciple
      g (chosenLocalModels g)

/-- Selected monotone prefixed subpath-merge value boundary. -/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessPrinciple
      g (chosenLocalModels g)

theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem_of_subpathMerge
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMerge :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSubpathMergeBranchDataWitnessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem
      X chosenLocalModels := by
  intro g
  exact
    pathLocalTransitionBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessPrinciple_of_subpathMerge
      (hMerge g)

theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem_of_unitSplit
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hUnit :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffUnitSplitBranchDataWitnessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem
      X chosenLocalModels := by
  intro g
  exact
    pathLocalTransitionBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessPrinciple_of_unitSplit
      (hUnit g)

theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffInteriorUnitSplitBranchDataWitnessTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g} :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffInteriorUnitSplitBranchDataWitnessTheorem
      X chosenLocalModels := by
  intro g
  exact pathLocalTransitionBasedWeakHandoffInteriorUnitSplitBranchDataWitnessPrinciple

theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffUnitSplitBranchDataWitnessTheorem_of_interior
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hInterior :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffInteriorUnitSplitBranchDataWitnessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffUnitSplitBranchDataWitnessTheorem
      X chosenLocalModels := by
  intro g
  exact
    pathLocalTransitionBasedWeakHandoffUnitSplitBranchDataWitnessPrinciple_of_interior
      (hInterior g)

theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem_of_interiorUnitSplit
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hInterior :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffInteriorUnitSplitBranchDataWitnessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem_of_unitSplit
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffUnitSplitBranchDataWitnessTheorem_of_interior
      hInterior)

theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem_of_prefixedSubpathMerge
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMerge :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffPrefixedSubpathMergeValueWitnessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem
      X chosenLocalModels := by
  intro g
  exact
    pathLocalTransitionBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessPrinciple_of_prefixedSubpathMerge
      (hMerge g)

theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem_of_monotoneSubpathMergeBranchData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMerge :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem
      X chosenLocalModels := by
  intro g
  exact
    pathLocalTransitionBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessPrinciple_of_monotoneSubpathMergeBranchData
      (hMerge g)

/-- Selected endpoint-normalization boundary from raw cut paths to public cuts. -/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessPrinciple
      x₀ g (chosenLocalModels g)

theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessTheorem_unconditional
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g} :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessPrinciple_unconditional
      x₀ g (chosenLocalModels g)

theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnRawCutReparamExplicitValueWitnessTheorem_of_subpathMerge
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMerge :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSubpathMergeBranchDataWitnessTheorem
        X chosenLocalModels)
    (hPrefMerge :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffPrefixedSubpathMergeValueWitnessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnRawCutReparamExplicitValueWitnessTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnRawCutReparamExplicitValueWitnessPrinciple_of_subpathMerge
      (hMerge g) (hPrefMerge g)

theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnRawCutReparamExplicitValueWitnessTheorem_of_monotoneSubpathMerge
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMerge :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem
        X chosenLocalModels)
    (hPrefMerge :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnRawCutReparamExplicitValueWitnessTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnRawCutReparamExplicitValueWitnessPrinciple_of_monotoneSubpathMerge
      (hMerge g) (hPrefMerge g)

theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem_of_subpathMerge_and_endpointNormalization
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMerge :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSubpathMergeBranchDataWitnessTheorem
        X chosenLocalModels)
    (hPrefMerge :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffPrefixedSubpathMergeValueWitnessTheorem
        X chosenLocalModels)
    (hNormalize :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple_of_subpathMerge_and_endpointNormalization
      (hMerge g) (hPrefMerge g) (hNormalize x₀ g)

theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem_of_monotoneSubpathMerge_and_endpointNormalization
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMerge :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem
        X chosenLocalModels)
    (hPrefMerge :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem
        X chosenLocalModels)
    (hNormalize :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple_of_monotoneSubpathMerge_and_endpointNormalization
      (hMerge g) (hPrefMerge g) (hNormalize x₀ g)

theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferTheorem_of_explicitValueWitness
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hExplicit :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferPrinciple_of_explicitValueWitness_unconditional
      (hExplicit x₀ g)

theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessTheorem_unconditional
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g} :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessPrinciple_unconditional
      x₀ g (chosenLocalModels g)

/--
Selected one-column chart-grid replacement principle for based weak handoff
skeletons.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnMovePrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnMovePrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected one-strip chart-grid replacement principle for based weak handoff
skeletons.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripMovePrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripMovePrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected chart-grid local replacement principle for based weak handoff
skeletons.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartGridMovePrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffHomotopyChartGridMovePrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected fixed-chart homotopy-grid move walk principle for based weak handoff
skeletons.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffFixedChartGridMoveWalkPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffFixedChartGridMoveWalkPrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected local-extension compatibility for terminal-sheet paths.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected existential local-extension theorem for terminal-sheet paths.

Unlike the coherent-choice principle above, this target is unconditional:
the appended terminal-sheet skeleton is constructed explicitly.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionExistenceTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionExistencePrinciple
      x₀ g (chosenLocalModels g)

/-- The explicit terminal-extension skeleton proves selected existential local extension. -/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionExistenceTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionExistenceTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionExistencePrinciple
      x₀ g (chosenLocalModels g)

/--
Selected same-path terminal-value uniqueness for based weak handoff skeletons.

This is the choice-independence boundary left after terminal-sheet extensions
are constructed explicitly.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected mutual vertex-refinement terminal-value comparison for based weak
handoff skeletons over the same representative path.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementTerminalValueTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementTerminalValuePrinciple
      x₀ g (chosenLocalModels g)

/--
Selected mutual vertex-refinement aligned-subdivision comparison.

This is the selected theorem-package form of the remaining combinatorial
boundary: the branch comparison is already local-analytic, so the only data
requested here is equality of the two mutually refined parameter lists.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected own-split parameter-alignment comparison.

This is the sharper finite-subdivision boundary behind common aligned mutual
vertex refinements: mutual endpoint-chart insertion is followed by one plain
split along the original vertices on each side; the lengths are already a
theorem, so this package only asks for pointwise agreement of the resulting
parameter lists.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected own-split parameter-permutation comparison.

This is the multiset form of the own-split boundary; sortedness converts it to
the pointwise alignment theorem above.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected finite same-path skeleton move-walk principle for based weak handoff
skeletons.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathSkeletonMoveWalkPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalkPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected common-refinement comparison principle for based weak handoff
skeletons over the same representative path.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffSamePathCommonComparisonPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected terminal-sheet extension-agreement principle for based weak handoff
skeletons.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetExtensionAgreementPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected PSL-level terminal-sheet extension-agreement principle for based weak
handoff skeletons.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetExtensionProjectionAgreementPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionProjectionAgreementPrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected coherent finite-grid/local-extension data for based weak handoff
continuation.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffHomotopyGridLocalExtensionData
        x₀ g (chosenLocalModels g))

/--
Selected coherent elementary-grid/local-extension data for based weak handoff
continuation.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionData
        x₀ g (chosenLocalModels g))

/--
Selected coherent elementary-grid/terminal-extension-agreement data for based
weak handoff continuation.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionAgreementDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
        x₀ g (chosenLocalModels g))

/--
Selected coherent elementary-grid/PSL-terminal-extension-agreement data for
based weak handoff continuation.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionProjectionAgreementDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData
        x₀ g (chosenLocalModels g))

/--
Selected canonical-terminal-sheet agreement with PSL monodromy for the
constructed canonical-cover map.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
        x₀ g (chosenLocalModels g))

/--
Selected terminal-Mobius PSL covariance for canonical-terminal-sheet agreement
data.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceDataPSL
        agreementContinuation)

/--
Selected transition-adjusted terminal-Mobius PSL covariance for
canonical-terminal-sheet agreement data.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceDataPSL
        agreementContinuation)

/--
Selected terminal-Mobius PSL covariance using the automatic endpoint chart
transition supplied by the local-transition atlas.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceDataPSL
        agreementContinuation)

/--
Selected automatic endpoint-transition terminal-Mobius PSL covariance with
holonomy derived from base-loop terminal continuation.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        agreementContinuation)

/--
Selected reduced derived-holonomy PSL covariance for canonical-sheet
agreement data.  The PSL identity and multiplication laws are recovered from
the derived loop-terminal classes, so this is the smaller monodromy boundary.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyDataPSL
        agreementContinuation)

/--
Selected canonical-loop covariance for canonical-sheet agreement data.  This
is smaller than reduced derived-holonomy covariance: it only asks for the
covariance formula for the canonical loop representative selected by
`Quot.out`.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceDataPSL
        agreementContinuation)

/--
Selected normalized canonical-loop projection propagation for
canonical-sheet agreement data.  This is the path-propagation form of the
canonical-loop covariance boundary.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationDataPSL
        agreementContinuation)

/--
Selected canonical-cover constancy of the normalized canonical-loop
projection.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverDataPSL
        agreementContinuation)

/--
Selected local constancy on the canonical cover of the normalized
canonical-loop projection.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverDataPSL
        agreementContinuation)

/--
Selected local-sheet constancy of the normalized canonical-loop projection.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyDataPSL
        agreementContinuation)

/--
Selected terminal-sheet transport of the normalized canonical-loop projection.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportDataPSL
        agreementContinuation)

/--
Selected value-equivariance plus terminal-Mobius projection-rigidity data
identifying the value holonomy with the derived loop-terminal PSL class.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionDataPSL
        agreementContinuation)

/--
Selected value-equivariance plus projection-rigidity data.

Compared with
`SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionTheoremPSL`,
this does not ask separately for the value holonomy to equal the derived
loop-terminal holonomy; that equality is forced by the base-loop case.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityDataPSL
        agreementContinuation)

/--
Selected terminal-formula PSL projection rigidity from deck equivariance of
the canonical-cover map.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityDataPSL
        agreementContinuation)

/--
Selected terminal-formula PSL projection faithfulness for terminal-sheet
agreement data.  This is the local mathematical boundary: once the two
terminal-sheet formulae agree as functions on the overlap neighborhood, their
PSL projections agree.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessDataPSL
        agreementContinuation)

/--
Selected PSL action faithfulness on the terminal coordinate agreement set for
terminal-sheet agreement data.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessDataPSL
        agreementContinuation)

/--
Selected three-point richness for terminal coordinate agreement sets in
terminal-sheet agreement data.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessDataPSL
        agreementContinuation)

/--
Selected nonempty-open-subset richness for terminal coordinate agreement sets
in terminal-sheet agreement data.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementDataPSL
        agreementContinuation)

/--
The selected terminal-coordinate nonempty-open boundary is unconditional for
terminal-sheet agreement data.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementTheoremPSL
      X chosenLocalModels := by
  intro x₀ g agreementContinuation
  exact
    ⟨agreementContinuation.toTerminalFormulaNonemptyOpenAgreementDataPSL⟩

/--
The selected terminal-coordinate three-point-richness boundary is
unconditional for terminal-sheet agreement data.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessTheoremPSL
      X chosenLocalModels := by
  intro x₀ g agreementContinuation
  exact
    ⟨agreementContinuation.toTerminalFormulaThreePointRichnessDataPSL⟩

/--
The selected terminal-coordinate PSL action-faithfulness boundary is
unconditional for terminal-sheet agreement data.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessTheoremPSL
      X chosenLocalModels := by
  intro x₀ g agreementContinuation
  exact
    ⟨agreementContinuation.toTerminalFormulaActionFaithfulnessDataPSL⟩

/--
The selected terminal-formula PSL projection-faithfulness boundary is
unconditional for terminal-sheet agreement data.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessTheoremPSL
      X chosenLocalModels := by
  intro x₀ g agreementContinuation
  exact
    ⟨agreementContinuation.toTerminalFormulaProjectionFaithfulnessDataPSL⟩

/--
The selected terminal-formula projection-rigidity boundary is unconditional
for terminal-sheet agreement data.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityTheoremPSL
      X chosenLocalModels := by
  intro x₀ g agreementContinuation
  exact
    ⟨agreementContinuation.toTerminalFormulaProjectionRigidityDataPSL⟩

/--
Selected PSL loop-equivariance for canonical-terminal-sheet agreement data.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
        agreementContinuation)

/--
Selected PSL loop-equivariance for canonical-terminal-sheet based weak handoff
continuation data.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetValueEquivarianceTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (continuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueEquivarianceDataPSL
        continuation)

/--
Selected PSL loop-equivariance for already constructed value-level finite-chain
terminal continuation data.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathChainTerminalBranchValueEquivarianceTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (chainTerminalContinuation :
      PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionChainTerminalBranchAnalyticContinuationValueEquivarianceDataPSL
        chainTerminalContinuation)

/--
Path-class continuation data, before loop monodromy/equivariance, for a fixed
selected local-transition atlas.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathClassContinuationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathClassLocalTransitionAnalyticContinuationData
        x₀ g (chosenLocalModels g))

/--
PSL-valued loop equivariance for already constructed path-class continuation
data, for a fixed selected local-transition atlas.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathClassEquivarianceTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (pathClassContinuation :
      PathClassLocalTransitionAnalyticContinuationData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathClassLocalTransitionAnalyticContinuationEquivarianceDataPSL
        pathClassContinuation)

/--
Path-class continuation plus PSL loop equivariance gives PSL path-class
monodromy for a selected local-transition atlas.
-/
def selectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL_of_selectedPathClassContinuation_and_selectedPathClassEquivariancePSL
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hContinuation :
      SelectedLocalTransitionModelAnalyticContinuationPathClassContinuationTheorem
        X chosenLocalModels)
    (hEquivariance :
      SelectedLocalTransitionModelAnalyticContinuationPathClassEquivarianceTheoremPSL
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
      X chosenLocalModels := by
  intro x₀ g
  rcases hContinuation x₀ g with ⟨C⟩
  rcases hEquivariance x₀ g C with ⟨E⟩
  exact
    ⟨E.toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL⟩

/--
Selected elementary grid-move walks imply the selected finite homotopy-grid
walk principle.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem_of_selectedElementaryGridMoveWalk
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hElementary :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffHomotopyGridWalkPrinciple_of_elementaryGridMoveWalkPrinciple
      (hElementary x₀ g basedWeakHandoffAlong)

/--
Selected decomposed one-column witnesses plus selected cut-reparameterization
transfer imply the selected public one-column value-witness theorem.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnValueWitnessTheorem_of_selectedDecomposed_and_selectedCutReparam
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hDecomp :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessTheorem
        X chosenLocalModels)
    (hCut :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnValueWitnessTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnValueWitnessPrinciple_of_decomposed_and_cutReparam
      (hDecomp x₀ g) (hCut x₀ g)

/--
Selected one-column value witnesses imply selected one-column grid moves;
same-path terminal-value uniqueness is already unconditional.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnMovePrincipleTheorem_of_selectedHomotopyChartStripColumnValueWitness
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hValue :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnValueWitnessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnMovePrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnMovePrinciple_of_valueWitness_unconditional
      (basedWeakHandoffAlong := basedWeakHandoffAlong)
      (hValue x₀ g)

/--
Selected one-column replacement implies selected one-strip replacement by
finite concatenation across the path-parameter subdivision.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripMovePrincipleTheorem_of_selectedHomotopyChartStripColumnMove
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hColumn :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnMovePrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripMovePrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffHomotopyChartStripMovePrinciple_of_columnMovePrinciple
      (hColumn x₀ g basedWeakHandoffAlong)

/--
Selected one-strip replacement implies selected chart-grid replacement by
finite concatenation of strips.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartGridMovePrincipleTheorem_of_selectedHomotopyChartStripMove
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hStrip :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripMovePrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartGridMovePrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffHomotopyChartGridMovePrinciple_of_stripMovePrinciple
      (hStrip x₀ g basedWeakHandoffAlong)

/--
Selected chart-grid local replacement implies selected elementary grid-move
walks; compactness of the homotopy square supplies the finite chart grid.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem_of_selectedHomotopyChartGridMove
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hChartGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartGridMovePrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffElementaryGridMoveWalkPrinciple_of_homotopyChartGridMovePrinciple
      (hChartGrid x₀ g basedWeakHandoffAlong)

/--
Selected chart-grid local replacement implies the selected finite
homotopy-grid walk principle.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem_of_selectedHomotopyChartGridMove
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hChartGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartGridMovePrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem_of_selectedElementaryGridMoveWalk
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem_of_selectedHomotopyChartGridMove
      hChartGrid)

/--
Selected fixed-chart grid walks imply selected elementary grid-move walks.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem_of_selectedFixedChartGridMoveWalk
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hFixed :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffFixedChartGridMoveWalkPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffElementaryGridMoveWalkPrinciple_of_fixedChartGridMoveWalkPrinciple
      (hFixed x₀ g basedWeakHandoffAlong)

/--
Selected fixed-chart grid walks imply the selected finite homotopy-grid walk
principle.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem_of_selectedFixedChartGridMoveWalk
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hFixed :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffFixedChartGridMoveWalkPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem_of_selectedElementaryGridMoveWalk
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem_of_selectedFixedChartGridMoveWalk
      hFixed)

/--
Selected finite homotopy-grid walks plus selected local extension imply the
selected terminal-sheet homotopy principle.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedLocalExtension
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hLocal :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyPrinciple_of_homotopyGridWalk_and_localExtension
      basedWeakHandoffAlong
      (hGrid x₀ g basedWeakHandoffAlong)
      (hLocal x₀ g basedWeakHandoffAlong)

/--
Selected elementary grid-move walks plus selected local extension imply the
selected terminal-sheet homotopy principle.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedElementaryGridMoveWalk_and_selectedLocalExtension
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hElementary :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
        X chosenLocalModels)
    (hLocal :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedLocalExtension
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem_of_selectedElementaryGridMoveWalk
      hElementary)
    hLocal

/--
Selected same-path terminal-value uniqueness gives selected terminal-sheet
local extension, using the explicit terminal-extension skeleton.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem_of_selectedSamePathTerminalValueUniqueness
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hUnique :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple_of_samePathTerminalValueUniqueness
      (hUnique x₀ g)

/--
Selected same-path skeleton move walks imply selected same-path
terminal-value uniqueness.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedSamePathSkeletonMoveWalk
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hWalk :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathSkeletonMoveWalkPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple_of_samePathSkeletonMoveWalk
      (hWalk x₀ g)

/--
Selected same-path skeleton move walks imply selected same-path
common-refinement comparisons.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonTheorem_of_selectedSamePathSkeletonMoveWalk
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hWalk :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathSkeletonMoveWalkPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffSamePathCommonComparisonPrinciple_of_samePathSkeletonMoveWalk
      (hWalk x₀ g)

/--
Selected same-path common-refinement comparisons imply selected common aligned
mutual vertex refinements.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem_of_selectedSamePathCommonComparison
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple_of_samePathCommonComparison
      (hComparison x₀ g)

/--
Selected own-split parameter alignment implies selected common aligned mutual
vertex refinements.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem_of_selectedOwnSplitParameterAlignment
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAlign :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple_of_ownSplitParameterAlignment
      (hAlign x₀ g)

/--
The selected own-split parameter-permutation theorem is unconditional: it is
only finite parameter-list bookkeeping for the chosen local-transition atlas.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g} :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationPrinciple

/--
The selected own-split parameter-alignment theorem is unconditional.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g} :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentPrinciple_unconditional

/--
The selected common aligned mutual-refinement theorem is unconditional.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g} :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple_unconditional

/--
The selected mutual vertex-refinement terminal-value theorem is unconditional.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementTerminalValueTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g} :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementTerminalValueTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementTerminalValuePrinciple_unconditional

/--
The selected same-path terminal-value uniqueness theorem is unconditional.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g} :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple_unconditional

/--
The selected terminal-sheet local-extension theorem is unconditional for any
chosen coherent based weak handoff skeletons.
-/
theorem selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g} :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple_unconditional

/--
Selected own-split parameter permutations imply selected own-split parameter
alignment.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem_of_selectedOwnSplitParameterPermutation
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hPerm :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentPrinciple_of_parameterPermutation
      (hPerm x₀ g)

/--
Selected own-split parameter permutations imply selected common aligned mutual
vertex refinements.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem_of_selectedOwnSplitParameterPermutation
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hPerm :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem_of_selectedOwnSplitParameterAlignment
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem_of_selectedOwnSplitParameterPermutation
      hPerm)

/--
Selected same-path common-refinement comparisons imply selected same-path
terminal-value uniqueness.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedSamePathCommonComparison
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple_of_samePathCommonComparison
      (hComparison x₀ g)

/--
Selected mutual vertex-refinement comparison implies selected same-path
terminal-value uniqueness.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedMutualVertexRefinementTerminalValue
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMutual :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementTerminalValueTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple_of_mutualVertexRefinementTerminalValue
      (hMutual x₀ g)

/--
Selected aligned mutual vertex refinements give selected mutual-refinement
terminal-value comparison.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementTerminalValueTheorem_of_selectedMutualVertexRefinementCommonAlignedSubdivision
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAlign :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementTerminalValueTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementTerminalValuePrinciple_of_mutualVertexRefinementCommonAlignedSubdivision
      (hAlign x₀ g)

/--
Selected aligned mutual vertex refinements give selected same-path
terminal-value uniqueness.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedMutualVertexRefinementCommonAlignedSubdivision
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAlign :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedMutualVertexRefinementTerminalValue
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementTerminalValueTheorem_of_selectedMutualVertexRefinementCommonAlignedSubdivision
      hAlign)

/--
Selected finite homotopy-grid walks plus selected same-path terminal-value
uniqueness imply the selected terminal-sheet homotopy principle.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedSamePathTerminalValueUniqueness
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hUnique :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedLocalExtension
    hGrid
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem_of_selectedSamePathTerminalValueUniqueness
      hUnique)

/--
Selected finite homotopy-grid walks plus selected same-path skeleton move walks
imply the selected terminal-sheet homotopy principle.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedSamePathSkeletonMoveWalk
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hWalk :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathSkeletonMoveWalkPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedSamePathTerminalValueUniqueness
    hGrid
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedSamePathSkeletonMoveWalk
      hWalk)

/--
Selected finite homotopy-grid walks plus selected same-path common-refinement
comparisons imply the selected terminal-sheet homotopy principle.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedSamePathTerminalValueUniqueness
    hGrid
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedSamePathCommonComparison
      hComparison)

/--
Selected elementary grid-move walks plus selected same-path skeleton move walks
imply the selected terminal-sheet homotopy principle.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedElementaryGridMoveWalk_and_selectedSamePathSkeletonMoveWalk
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hElementary :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
        X chosenLocalModels)
    (hWalk :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathSkeletonMoveWalkPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedElementaryGridMoveWalk_and_selectedLocalExtension
    hElementary
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem_of_selectedSamePathTerminalValueUniqueness
      (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedSamePathSkeletonMoveWalk
        hWalk))

/--
Selected elementary grid-move walks plus selected same-path common-refinement
comparisons imply the selected terminal-sheet homotopy principle.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedElementaryGridMoveWalk_and_selectedSamePathCommonComparison
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hElementary :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedElementaryGridMoveWalk_and_selectedLocalExtension
    hElementary
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem_of_selectedSamePathTerminalValueUniqueness
      (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedSamePathCommonComparison
        hComparison))

/--
Selected elementary grid-move walks plus same-path terminal-value uniqueness
imply the selected terminal-sheet homotopy principle.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedElementaryGridMoveWalk_and_selectedSamePathTerminalValueUniqueness
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hElementary :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
        X chosenLocalModels)
    (hUnique :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedElementaryGridMoveWalk_and_selectedLocalExtension
    hElementary
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem_of_selectedSamePathTerminalValueUniqueness
      hUnique)

/--
Selected terminal-sheet extension agreement implies selected terminal-sheet
local extension.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem_of_selectedTerminalSheetExtensionAgreement
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetExtensionAgreementPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple_of_terminalSheetExtensionAgreement
      (hAgreement x₀ g basedWeakHandoffAlong)

/--
Selected exact terminal-sheet extension agreement forgets to the selected
PSL-level extension agreement.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetExtensionProjectionAgreementPrincipleTheorem_of_selectedTerminalSheetExtensionAgreement
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetExtensionAgreementPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetExtensionProjectionAgreementPrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffTerminalSheetExtensionProjectionAgreementPrinciple_of_extensionAgreement
      (hAgreement x₀ g basedWeakHandoffAlong)

/--
Selected PSL-level terminal-sheet extension agreement implies selected
terminal-sheet local extension.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem_of_selectedTerminalSheetExtensionProjectionAgreement
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetExtensionProjectionAgreementPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple_of_terminalSheetExtensionProjectionAgreement
      (hAgreement x₀ g basedWeakHandoffAlong)

/--
Selected elementary grid-move walks plus selected terminal-sheet local
extension construct coherent elementary-grid/local-extension data.  The
remaining choices are the already-proved compactness choices of based weak
handoff skeletons along representative paths.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem_of_selectedElementaryGridMoveWalk_and_selectedLocalExtension
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hElementary :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
        X chosenLocalModels)
    (hLocal :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem
      X chosenLocalModels := by
  intro x₀ g
  let basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p :=
    fun {_} p =>
      Classical.choice
        (exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
          (chosenLocalModels g) p)
  exact
    ⟨{ basedWeakHandoffAlong := basedWeakHandoffAlong
       elementaryGridMoveWalk := hElementary x₀ g basedWeakHandoffAlong
       terminalSheetLocalExtension := hLocal x₀ g basedWeakHandoffAlong }⟩

/--
Selected finite homotopy-grid walks plus selected terminal-sheet local
extension construct coherent finite-grid/local-extension data.  This is the
homotopy-grid analogue of the elementary-grid constructor above.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem_of_selectedHomotopyGridWalk_and_selectedLocalExtension
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hLocal :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem
      X chosenLocalModels := by
  intro x₀ g
  let basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p :=
    fun {_} p =>
      Classical.choice
        (exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
          (chosenLocalModels g) p)
  exact
    ⟨{ basedWeakHandoffAlong := basedWeakHandoffAlong
       homotopyGridWalk := hGrid x₀ g basedWeakHandoffAlong
       terminalSheetLocalExtension := hLocal x₀ g basedWeakHandoffAlong }⟩

/--
Selected elementary grid-move walks plus same-path terminal-value uniqueness
construct coherent elementary-grid/local-extension data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem_of_selectedElementaryGridMoveWalk_and_selectedSamePathTerminalValueUniqueness
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hElementary :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
        X chosenLocalModels)
    (hUnique :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem_of_selectedElementaryGridMoveWalk_and_selectedLocalExtension
    hElementary
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem_of_selectedSamePathTerminalValueUniqueness
      hUnique)

/--
Selected elementary grid-move walks plus same-path skeleton move walks
construct coherent elementary-grid/local-extension data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem_of_selectedElementaryGridMoveWalk_and_selectedSamePathSkeletonMoveWalk
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hElementary :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
        X chosenLocalModels)
    (hWalk :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathSkeletonMoveWalkPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem_of_selectedElementaryGridMoveWalk_and_selectedSamePathTerminalValueUniqueness
    hElementary
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedSamePathSkeletonMoveWalk
      hWalk)

/--
Selected elementary grid-move walks plus same-path common-refinement
comparisons construct coherent elementary-grid/local-extension data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem_of_selectedElementaryGridMoveWalk_and_selectedSamePathCommonComparison
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hElementary :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem_of_selectedElementaryGridMoveWalk_and_selectedSamePathTerminalValueUniqueness
    hElementary
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedSamePathCommonComparison
      hComparison)

/--
Selected finite homotopy-grid walks plus same-path terminal-value uniqueness
construct coherent finite-grid/local-extension data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem_of_selectedHomotopyGridWalk_and_selectedSamePathTerminalValueUniqueness
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hUnique :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem_of_selectedHomotopyGridWalk_and_selectedLocalExtension
    hGrid
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem_of_selectedSamePathTerminalValueUniqueness
      hUnique)

/--
Selected finite homotopy-grid walks plus same-path skeleton move walks
construct coherent finite-grid/local-extension data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem_of_selectedHomotopyGridWalk_and_selectedSamePathSkeletonMoveWalk
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hWalk :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathSkeletonMoveWalkPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem_of_selectedHomotopyGridWalk_and_selectedSamePathTerminalValueUniqueness
    hGrid
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedSamePathSkeletonMoveWalk
      hWalk)

/--
Selected finite homotopy-grid walks plus same-path common-refinement
comparisons construct coherent finite-grid/local-extension data.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem_of_selectedHomotopyGridWalk_and_selectedSamePathCommonComparison
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hComparison :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathCommonComparisonPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem_of_selectedHomotopyGridWalk_and_selectedSamePathTerminalValueUniqueness
    hGrid
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedSamePathCommonComparison
      hComparison)

/--
Selected elementary grid-move walks plus selected terminal-sheet extension
agreement construct coherent elementary-grid/terminal-extension-agreement data.
The representative-path handoff skeletons are chosen from the compactness
existence theorem.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionAgreementDataTheorem_of_selectedElementaryGridMoveWalk_and_selectedTerminalSheetExtensionAgreement
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hElementary :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
        X chosenLocalModels)
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetExtensionAgreementPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionAgreementDataTheorem
      X chosenLocalModels := by
  intro x₀ g
  let basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p :=
    fun {_} p =>
      Classical.choice
        (exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
          (chosenLocalModels g) p)
  exact
    ⟨{ basedWeakHandoffAlong := basedWeakHandoffAlong
       elementaryGridMoveWalk := hElementary x₀ g basedWeakHandoffAlong
       terminalSheetExtensionAgreement :=
        hAgreement x₀ g basedWeakHandoffAlong }⟩

/--
Selected elementary grid-move walks plus selected PSL terminal-sheet extension
agreement construct coherent elementary-grid/PSL-terminal-extension-agreement
data.  The representative-path handoff skeletons are chosen from the
compactness existence theorem.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionProjectionAgreementDataTheorem_of_selectedElementaryGridMoveWalk_and_selectedTerminalSheetExtensionProjectionAgreement
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hElementary :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
        X chosenLocalModels)
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetExtensionProjectionAgreementPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionProjectionAgreementDataTheorem
      X chosenLocalModels := by
  intro x₀ g
  let basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p :=
    fun {_} p =>
      Classical.choice
        (exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
          (chosenLocalModels g) p)
  exact
    ⟨{ basedWeakHandoffAlong := basedWeakHandoffAlong
       elementaryGridMoveWalk := hElementary x₀ g basedWeakHandoffAlong
       terminalSheetExtensionProjectionAgreement :=
        hAgreement x₀ g basedWeakHandoffAlong }⟩

/--
Selected elementary grid-move walks plus selected terminal-extension
agreement imply the selected terminal-sheet homotopy principle.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedElementaryGridMoveWalk_and_selectedTerminalSheetExtensionAgreement
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hElementary :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
        X chosenLocalModels)
    (hAgreement :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetExtensionAgreementPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedElementaryGridMoveWalk_and_selectedLocalExtension
    hElementary
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem_of_selectedTerminalSheetExtensionAgreement
      hAgreement)

/--
Selected coherent terminal-sheet homotopy data give selected terminal-sheet
agreement.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem_of_selectedTerminalSheetHomotopyData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hData :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyDataTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
      X chosenLocalModels := by
  intro x₀ g
  rcases hData x₀ g with ⟨D⟩
  exact ⟨D.toCanonicalSheetAgreementData⟩

/--
Selected coherent finite-grid/local-extension data give selected coherent
terminal-sheet homotopy data.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyDataTheorem_of_selectedHomotopyGridLocalExtensionData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hData :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyDataTheorem
      X chosenLocalModels := by
  intro x₀ g
  rcases hData x₀ g with ⟨D⟩
  exact ⟨D.toTerminalSheetHomotopyData⟩

/--
Selected coherent elementary-grid/local-extension data give selected coherent
finite-grid/local-extension data.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem_of_selectedElementaryGridLocalExtensionData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hData :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem
      X chosenLocalModels := by
  intro x₀ g
  rcases hData x₀ g with ⟨D⟩
  exact ⟨D.toHomotopyGridLocalExtensionData⟩

/--
Selected coherent elementary-grid/local-extension data give selected coherent
terminal-sheet homotopy data.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyDataTheorem_of_selectedElementaryGridLocalExtensionData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hData :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyDataTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyDataTheorem_of_selectedHomotopyGridLocalExtensionData
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem_of_selectedElementaryGridLocalExtensionData
      hData)

/--
Selected coherent elementary-grid/terminal-extension-agreement data give
selected coherent elementary-grid/local-extension data.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem_of_selectedElementaryGridExtensionAgreementData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hData :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionAgreementDataTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem
      X chosenLocalModels := by
  intro x₀ g
  rcases hData x₀ g with ⟨D⟩
  exact ⟨D.toElementaryGridLocalExtensionData⟩

/--
Selected coherent elementary-grid/terminal-extension-agreement data forget to
selected coherent elementary-grid/PSL-terminal-extension-agreement data.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionProjectionAgreementDataTheorem_of_selectedElementaryGridExtensionAgreementData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hData :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionAgreementDataTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionProjectionAgreementDataTheorem
      X chosenLocalModels := by
  intro x₀ g
  rcases hData x₀ g with ⟨D⟩
  exact ⟨D.toElementaryGridExtensionProjectionAgreementData⟩

/--
Selected coherent elementary-grid/PSL-terminal-extension-agreement data give
selected coherent elementary-grid/local-extension data.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem_of_selectedElementaryGridExtensionProjectionAgreementData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hData :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionProjectionAgreementDataTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem
      X chosenLocalModels := by
  intro x₀ g
  rcases hData x₀ g with ⟨D⟩
  exact ⟨D.toElementaryGridLocalExtensionData⟩

/--
Selected coherent elementary-grid/terminal-extension-agreement data give
selected coherent finite-grid/local-extension data.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem_of_selectedElementaryGridExtensionAgreementData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hData :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionAgreementDataTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem_of_selectedElementaryGridLocalExtensionData
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem_of_selectedElementaryGridExtensionAgreementData
      hData)

/--
Selected coherent elementary-grid/terminal-extension-agreement data give
selected coherent terminal-sheet homotopy data.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyDataTheorem_of_selectedElementaryGridExtensionAgreementData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hData :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionAgreementDataTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyDataTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyDataTheorem_of_selectedElementaryGridLocalExtensionData
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem_of_selectedElementaryGridExtensionAgreementData
      hData)

/--
Selected coherent finite-grid/local-extension data give selected
terminal-sheet agreement.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem_of_selectedHomotopyGridLocalExtensionData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hData :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem_of_selectedTerminalSheetHomotopyData
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyDataTheorem_of_selectedHomotopyGridLocalExtensionData
      hData)

/--
Selected coherent elementary-grid/local-extension data give selected
terminal-sheet agreement.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem_of_selectedElementaryGridLocalExtensionData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hData :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem_of_selectedHomotopyGridLocalExtensionData
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridLocalExtensionDataTheorem_of_selectedElementaryGridLocalExtensionData
      hData)

/--
Selected coherent elementary-grid/terminal-extension-agreement data give
selected terminal-sheet agreement.
-/
noncomputable def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem_of_selectedElementaryGridExtensionAgreementData
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hData :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridExtensionAgreementDataTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem_of_selectedElementaryGridLocalExtensionData
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridLocalExtensionDataTheorem_of_selectedElementaryGridExtensionAgreementData
      hData)

end HyperbolicMetric

end

end JJMath
