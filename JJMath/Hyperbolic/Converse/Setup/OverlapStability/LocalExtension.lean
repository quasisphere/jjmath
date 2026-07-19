import JJMath.Hyperbolic.Converse.Setup.ChartFrames

/-!
# Split overlap-stability setup declarations
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]


/--
Connected-overlap extension target for pointed hyperbolic local chart matches.

Once a real Mobius transformation matches the two local isometries at the
chosen point with the correct first-order data, the identity principle/local
isometry uniqueness argument should propagate the equality across the whole
preconnected overlap.  The present predicate records the propagated conclusion
from the pointed representative.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
    HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
      IsPreconnected (U.domain ∩ V.domain) →
        ∀ x, x ∈ U.domain → x ∈ V.domain →
          V.toUpperHalfPlane x =
            realMobiusRepresentativeAction A (U.toUpperHalfPlane x)

/--
Componentwise extension target for pointed hyperbolic local-chart matches.

This is the natural local-uniqueness boundary for analytic continuation on
possibly disconnected overlaps: the pointed match propagates exactly on the
connected component of `U.domain ∩ V.domain` containing the pointed match.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
    HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
      ∀ x, x ∈ U.domain → x ∈ V.domain →
        x ∈ connectedComponentIn (U.domain ∩ V.domain) x₀ →
          V.toUpperHalfPlane x =
            realMobiusRepresentativeAction A (U.toUpperHalfPlane x)

/--
Pointed transition target on the actual selected off-diagonal surface overlaps.

This is weaker than asking for pointed transitions for all hyperbolic local
charts: it only asks for one pointed real-Mobius match on each nonempty
overlap produced by the selected surface branch predata.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g)
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas),
    ∀ x y : X, x ≠ y →
      Set.Nonempty
        ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) →
      ∃ (x₀ : X) (A : RealMobiusRepresentative),
        HyperbolicLocalChartPointedRealMobiusTransition
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
          A x₀

/--
Pointwise selected-overlap pointed transition target for one Liouville metric
formula atlas.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) : Prop :=
  ∀ (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas),
    ∀ x y : X, x ≠ y →
      Set.Nonempty
        ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) →
      ∃ (x₀ : X) (A : RealMobiusRepresentative),
        HyperbolicLocalChartPointedRealMobiusTransition
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
          A x₀

/--
Chart-compatibility for the actual coordinate pullback formulae carried by a
selected surface predata object.

This is sharper than a global chart-compatibility theorem for all coordinate
pullback formulae: it only asks for the branches selected in one surface
predata object.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreDataCoordinateEqOnChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas) :
    Prop :=
  ∀ x x₀ : X,
    x₀ ∈
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).pullbackFormula).domain →
      Set.EqOn
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).pullbackFormula).coordinate
        (chartAt ℂ x₀)
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).pullbackFormula).domain

/--
Local chart-compatibility for the actual coordinate pullback formulae carried
by a selected surface predata object.

Unlike `SurfaceRealUpperHalfPlaneBranchAtlasPreDataCoordinateEqOnChartAt`,
this asks only for the pointwise ambient-coordinate identity needed to extract
one-jet data at `x₀`.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreDataCoordinateEventuallyEqOnChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas) :
    Prop :=
  ∀ x x₀ : X,
    x₀ ∈
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).pullbackFormula).domain →
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).pullbackFormula)
        x₀

/--
Domainwise equality with `chartAt x₀` implies the local ambient-coordinate
compatibility needed for selected one-jet extraction.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataCoordinateEventuallyEqOnChartAt_of_coordinateEqOnChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    {preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas}
    (hChart :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataCoordinateEqOnChartAt
        preData) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataCoordinateEventuallyEqOnChartAt
      preData := by
  intro x x₀ hx₀
  exact
    CoordinateUpperHalfPlanePullbackFormula.ambientCoordinateEventuallyEqAt_of_eqOn_chartAt
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).pullbackFormula)
      hx₀ (hChart x x₀ hx₀)

/--
Global pointed matching for all hyperbolic local charts supplies pointed
matches on the actual selected off-diagonal surface overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem_of_localChartPointedTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem
      X := by
  intro g metricFormulaAtlas preData x y hxy hne
  let U :=
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
  let V :=
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
  rcases hne with ⟨x₀, hxU, hxV⟩
  rcases hPoint g U V x₀ hxU hxV with ⟨A, hA⟩
  exact ⟨x₀, A, hA⟩

/--
Pointwise version: global pointed matching for all hyperbolic local charts
supplies pointed matches on the actual selected off-diagonal overlaps for one
Liouville formula atlas.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor_of_localChartPointedTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor
      metricFormulaAtlas := by
  intro preData x y hxy hne
  let U :=
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
  let V :=
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
  rcases hne with ⟨x₀, hxU, hxV⟩
  rcases hPoint g U V x₀ hxU hxV with ⟨A, hA⟩
  exact ⟨x₀, A, hA⟩

/--
Pointed derivative data for coordinate pullback formulae supplies pointed
matches on the actual selected off-diagonal surface overlaps.  This is the
selected-branch version of the metric-frame argument: the two compared charts
are known to arise from coordinate pullback formulae, so no theorem about
arbitrary hyperbolic local charts is needed.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem_of_coordinatePullbackFormulaPointedDerivativeData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hData :
      CoordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem
      X := by
  intro g metricFormulaAtlas preData x y hxy hne
  let Sx := (preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x
  let Sy := (preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y
  let Fx := Sx.pullbackFormula
  let Fy := Sy.pullbackFormula
  rcases hne with ⟨x₀, hxU, hxV⟩
  have hxFx : x₀ ∈ Fx.domain := by
    simpa [Sx, Fx, LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart]
      using hxU
  have hxFy : x₀ ∈ Fy.domain := by
    simpa [Sy, Fy, LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart]
      using hxV
  rcases hData g Fx x₀ hxFx with ⟨DFx⟩
  rcases hData g Fy x₀ hxFy with ⟨DFy⟩
  rcases
      HyperbolicLocalChartPointedRealMobiusTransition.exists_of_coordinateDerivativeData
        DFx DFy with
    ⟨A, hA⟩
  refine ⟨x₀, A, ?_⟩
  simpa [Sx, Sy, Fx, Fy, LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart]
    using hA

/--
Pointwise version: coordinate pullback formula pointed derivative data
supplies pointed matches on the actual selected off-diagonal overlaps of one
Liouville formula atlas.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor_of_coordinatePullbackFormulaPointedDerivativeData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hData :
      CoordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor
      metricFormulaAtlas := by
  intro preData x y hxy hne
  exact
    surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem_of_coordinatePullbackFormulaPointedDerivativeData
      hData g metricFormulaAtlas preData x y hxy hne

/--
Local chart-compatibility for the actual selected predata supplies pointed
matches on its nonempty off-diagonal overlaps.

This version uses only the pointwise ambient-coordinate identity at the chosen
overlap point, rather than domainwise equality with `chartAt`.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionForPreData_of_coordinateEventuallyEqOnChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hChart :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataCoordinateEventuallyEqOnChartAt
        preData) :
    ∀ x y : X, x ≠ y →
      Set.Nonempty
        ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) →
      ∃ (x₀ : X) (A : RealMobiusRepresentative),
        HyperbolicLocalChartPointedRealMobiusTransition
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
          A x₀ := by
  intro x y hxy hne
  let Sx := (preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x
  let Sy := (preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y
  let Fx := Sx.pullbackFormula
  let Fy := Sy.pullbackFormula
  rcases hne with ⟨x₀, hxU, hxV⟩
  have hxFx : x₀ ∈ Fx.domain := by
    simpa [Sx, Fx, LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart]
      using hxU
  have hxFy : x₀ ∈ Fy.domain := by
    simpa [Sy, Fy, LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart]
      using hxV
  have hCoordFx :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        Fx x₀ := by
    simpa [Sx, Fx] using hChart x x₀ hxFx
  have hCoordFy :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        Fy x₀ := by
    simpa [Sy, Fy] using hChart y x₀ hxFy
  let DFx :
      HyperbolicLocalChartPointedCoordinateDerivativeData
        Fx.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ :=
    CoordinateUpperHalfPlanePullbackFormula.toHyperbolicLocalChartPointedCoordinateDerivativeData_of_coordinateEventuallyEq
      Fx hxFx hCoordFx
  let DFy :
      HyperbolicLocalChartPointedCoordinateDerivativeData
        Fy.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ :=
    CoordinateUpperHalfPlanePullbackFormula.toHyperbolicLocalChartPointedCoordinateDerivativeData_of_coordinateEventuallyEq
      Fy hxFy hCoordFy
  rcases
      HyperbolicLocalChartPointedRealMobiusTransition.exists_of_coordinateDerivativeData
        DFx DFy with
    ⟨A, hA⟩
  refine ⟨x₀, A, ?_⟩
  simpa [Sx, Sy, Fx, Fy, LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart]
    using hA

/--
Chart-compatibility for the actual selected predata supplies pointed matches
on its nonempty off-diagonal overlaps.

This is the selected-predata version of the coordinate-pullback frame
normalization: the derivative data are extracted only for the two selected
branches at the chosen overlap point.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionForPreData_of_coordinateEqOnChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hChart :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataCoordinateEqOnChartAt
        preData) :
    ∀ x y : X, x ≠ y →
      Set.Nonempty
        ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) →
      ∃ (x₀ : X) (A : RealMobiusRepresentative),
        HyperbolicLocalChartPointedRealMobiusTransition
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
          A x₀ := by
  intro x y hxy hne
  let Sx := (preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x
  let Sy := (preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y
  let Fx := Sx.pullbackFormula
  let Fy := Sy.pullbackFormula
  rcases hne with ⟨x₀, hxU, hxV⟩
  have hxFx : x₀ ∈ Fx.domain := by
    simpa [Sx, Fx, LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart]
      using hxU
  have hxFy : x₀ ∈ Fy.domain := by
    simpa [Sy, Fy, LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart]
      using hxV
  have hEqFx : Set.EqOn Fx.coordinate (chartAt ℂ x₀) Fx.domain := by
    simpa [Sx, Fx] using hChart x x₀ hxFx
  have hEqFy : Set.EqOn Fy.coordinate (chartAt ℂ x₀) Fy.domain := by
    simpa [Sy, Fy] using hChart y x₀ hxFy
  let DFx :
      HyperbolicLocalChartPointedCoordinateDerivativeData
        Fx.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ :=
    CoordinateUpperHalfPlanePullbackFormula.toHyperbolicLocalChartPointedCoordinateDerivativeData
      Fx hxFx hEqFx
      (CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeNormSqAt_of_eqOn_chartAt
        Fx hxFx hEqFx)
  let DFy :
      HyperbolicLocalChartPointedCoordinateDerivativeData
        Fy.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ :=
    CoordinateUpperHalfPlanePullbackFormula.toHyperbolicLocalChartPointedCoordinateDerivativeData
      Fy hxFy hEqFy
      (CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeNormSqAt_of_eqOn_chartAt
        Fy hxFy hEqFy)
  rcases
      HyperbolicLocalChartPointedRealMobiusTransition.exists_of_coordinateDerivativeData
        DFx DFy with
    ⟨A, hA⟩
  refine ⟨x₀, A, ?_⟩
  simpa [Sx, Sy, Fx, Fy, LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart]
    using hA

/--
Coordinate derivative data supplies pointed matches on the actual selected
off-diagonal overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem_of_coordinateDerivativeData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem_of_localChartPointedTransitions
    (hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_coordinateDerivativeData_proved
      hDeriv)

/--
Pointwise version: coordinate derivative data supplies pointed matches on the
actual selected off-diagonal overlaps of one Liouville formula atlas.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor_of_coordinateDerivativeData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hDeriv :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor
      metricFormulaAtlas :=
  surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor_of_localChartPointedTransitions
    (hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_coordinateDerivativeData_proved
      hDeriv)

/--
Nonzero coordinate derivatives and the Poincare pullback squared-density
formula supply pointed matches on selected off-diagonal overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem_of_pullbackSquaredDensity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv : HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull : HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem_of_coordinateDerivativeData
    (hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula
      hDeriv hPull)

/--
The Poincare pullback squared-density formula alone supplies pointed matches
on selected off-diagonal overlaps; nonzero coordinate derivatives follow from
positivity of the source conformal density.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem_of_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull : HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem_of_coordinateDerivativeData
    (hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula_proved
      hPull)

/--
Pointwise version: nonzero coordinate derivatives and the Poincare pullback
squared-density formula supply pointed matches for one Liouville formula
atlas.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor_of_pullbackSquaredDensity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hDeriv : HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull : HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor
      metricFormulaAtlas :=
  surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor_of_coordinateDerivativeData
    (hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula
      hDeriv hPull)

/--
Pointwise version: the Poincare pullback squared-density formula alone
supplies pointed matches for one Liouville formula atlas.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor_of_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hPull : HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor
      metricFormulaAtlas :=
  surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionFor_of_coordinateDerivativeData
    (hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula_proved
      hPull)

/--
The equality locus of a pointed real-Mobius comparison of two hyperbolic local
charts, viewed as a subset of the common overlap.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) (A : RealMobiusRepresentative) :
    Set {x : X // x ∈ U.domain ∩ V.domain} :=
  {x | V.toUpperHalfPlane (x : X) =
      realMobiusRepresentativeAction A (U.toUpperHalfPlane (x : X))}

/--
The first-order frame-match locus of a real-Mobius comparison of two
hyperbolic local charts, viewed as a subset of the common overlap.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) (A : RealMobiusRepresentative) :
    Set {x : X // x ∈ U.domain ∩ V.domain} :=
  {x | HyperbolicLocalChartPointedFirstOrderMatch U V A (x : X)}

/--
The concrete value-plus-derivative locus for a real-Mobius comparison of two
hyperbolic local charts.

This is the same mathematical condition as the abstract first-order frame
match once pointed coordinate-derivative data is available for both charts.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) (A : RealMobiusRepresentative) :
    Set {x : X // x ∈ U.domain ∩ V.domain} :=
  {x |
    V.toUpperHalfPlane (x : X) =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane (x : X)) ∧
      HyperbolicLocalChartConcreteFirstOrderMatch U V A (x : X)}

/--
%%handwave
name: Equivalence of intrinsic and coordinate first-order matching loci
statement:
  Suppose every hyperbolic local chart has normalized nonzero coordinate-derivative data at each point. For charts \(U,V\) and a real Mobius transformation \(A\), the locus where their intrinsic oriented frames match through \(A\) equals the locus where
  \[
    V(x)=A(U(x)),\qquad V'(x)=A'(U(x))U'(x)
  \]
  in a common coordinate.
proof:
  Intrinsic frame matching directly gives the value and coordinate derivative equations. Conversely, use the normalized derivative data of \(U\) and \(V\) to turn those two coordinate equations into equality of the oriented hyperbolic frames.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet_eq_concreteFirstOrderMatchSet_of_coordinateDerivativeData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hData :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X)
    {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) (A : RealMobiusRepresentative) :
    pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet U V A =
      pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSet
        U V A := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.value_eq, hx.concreteFirstOrderMatch⟩
  · intro hx
    rcases hData g U (x : X) x.property.1 with ⟨DU⟩
    rcases hData g V (x : X) x.property.2 with ⟨DV⟩
    exact
      HyperbolicLocalChartPointedFirstOrderMatch_of_concreteFirstOrderMatch
        DU DV hx.1 hx.2

/--
The one-jet equality locus of a real-Mobius comparison of two hyperbolic local
charts, viewed as a subset of the common overlap.

This is the corrected local uniqueness locus: value equality alone does not
determine a holomorphic hyperbolic local isometry, but value plus the oriented
first-order frame does.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) (A : RealMobiusRepresentative) :
    Set {x : X // x ∈ U.domain ∩ V.domain} :=
  {x | V.toUpperHalfPlane (x : X) =
          realMobiusRepresentativeAction A (U.toUpperHalfPlane (x : X)) ∧
      HyperbolicLocalChartPointedFirstOrderMatch U V A (x : X)}

/--
%%handwave
name: The one-jet locus is the oriented-frame matching locus
statement:
  For hyperbolic local charts \(U,V\) and a real Mobius transformation \(A\), the locus where both their values and oriented first-order frames match through \(A\) is exactly the oriented-frame matching locus.
proof:
  One-jet matching contains frame matching by definition, while the oriented-frame relation already includes the equality \(V(x)=A(U(x))\).
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet_eq_firstOrderMatchSet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) (A : RealMobiusRepresentative) :
    pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet U V A =
      pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet U V A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨hx.value_eq, hx⟩

/--
The pullback, along a surface coordinate, of the coordinate-branch one-jet
equality locus.

This is the concrete same-coordinate surface version of the one-jet locus:
the surface point is first sent to the local complex coordinate, where the
Schwarzian branch package has the value-and-derivative one-jet predicate.
-/
def localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : LocalLiouvilleMetricFormula X g)
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) :
    Set {x : X // x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain} :=
  {x |
    (⟨F.coordinate (x : X), x.property.2⟩ :
      {z : ℂ // z ∈ H₁.domain ∩ H₂.domain}) ∈
        pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A}

/--
Continuity target for hyperbolic local charts on their domains.

For the present lightweight chart structure this is a theorem target, because
the holomorphicity/local-isometry fields are still abstract propositions.
-/
def HyperbolicLocalChartContinuousOnDomainTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U : HyperbolicLocalChart X g),
    Continuous (fun x : {x : X // x ∈ U.domain} ↦ U.toUpperHalfPlane (x : X))

/--
%%handwave
name: Continuity of a hyperbolic local chart on its domain
statement:
  Every hyperbolic local chart \(U\) defines a continuous map \(U:\operatorname{dom}(U)\to\mathbb H\).
proof:
  The stored surface coordinate is continuous on the chart domain. Its values lie in the coordinate domain of the stored holomorphic upper-half-plane map, which is continuous there. Compose the two maps and use the stored coordinate formula for \(U\).
-/
theorem hyperbolicLocalChartContinuousOnDomainTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] :
    HyperbolicLocalChartContinuousOnDomainTheorem X := by
  intro g U
  let L := U.local_isometry
  have hCoordinate : ContinuousOn L.coordinate U.domain :=
    (L.chart.continuousOn_toFun.mono L.domain_subset_chart_source).congr
      L.coordinate_eq_chart
  have hCoordinateSubtype :
      Continuous (fun x : {x : X // x ∈ U.domain} ↦ L.coordinate (x : X)) := by
    simpa [Set.restrict] using
      (continuousOn_iff_continuous_restrict.mp hCoordinate)
  let toCoordinateDomain :
      {x : X // x ∈ U.domain} → {z : ℂ // z ∈ L.coordinateDomain} :=
    fun x ↦ ⟨L.coordinate (x : X), L.coordinate_mem_domain (x : X) x.property⟩
  have hToCoordinateDomain : Continuous toCoordinateDomain :=
    hCoordinateSubtype.subtype_mk
      (fun x ↦ L.coordinate_mem_domain (x : X) x.property)
  have hLocalMapVal :
      ContinuousOn (fun z : ℂ ↦ (L.localMap z : ℂ))
        L.coordinateDomain := by
    intro z hz
    exact (L.holomorphic_on_domain z hz).continuousAt.continuousWithinAt
  have hLocalMapValSubtype :
      Continuous
        (fun z : {z : ℂ // z ∈ L.coordinateDomain} ↦
          (L.localMap (z : ℂ) : ℂ)) := by
    simpa [Set.restrict] using
      (continuousOn_iff_continuous_restrict.mp hLocalMapVal)
  have hLocalMapSubtype :
      Continuous
        (fun z : {z : ℂ // z ∈ L.coordinateDomain} ↦
          L.localMap (z : ℂ)) := by
    exact continuous_induced_rng.mpr (by
      simpa [Function.comp_def] using hLocalMapValSubtype)
  have hComp :
      Continuous
        (fun x : {x : X // x ∈ U.domain} ↦
          L.localMap (L.coordinate (x : X))) := by
    simpa [toCoordinateDomain] using
      hLocalMapSubtype.comp hToCoordinateDomain
  exact
    hComp.congr
      (fun x ↦ (L.toUpperHalfPlane_eq (x : X) x.property).symm)

/--
Continuity target for the two maps whose equality defines the local-chart
real-Mobius equality locus.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        Continuous
          (fun x : {x : X // x ∈ U.domain ∩ V.domain} ↦
            V.toUpperHalfPlane (x : X)) ∧
        Continuous
          (fun x : {x : X // x ∈ U.domain ∩ V.domain} ↦
            realMobiusRepresentativeAction A (U.toUpperHalfPlane (x : X)))

/--
Continuity of local charts on their domains, together with continuity of the
real Mobius action, gives continuity of the two maps compared in the equality
locus.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem_of_chart_continuity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hChart : HyperbolicLocalChartContinuousOnDomainTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem X := by
  intro g U V A x₀ _hpoint
  let overlap : Set X := U.domain ∩ V.domain
  let toUDomain : overlap → {x : X // x ∈ U.domain} :=
    fun x ↦ ⟨x, x.property.1⟩
  let toVDomain : overlap → {x : X // x ∈ V.domain} :=
    fun x ↦ ⟨x, x.property.2⟩
  have htoU : Continuous toUDomain := by
    exact continuous_subtype_val.subtype_mk (fun x ↦ x.property.1)
  have htoV : Continuous toVDomain := by
    exact continuous_subtype_val.subtype_mk (fun x ↦ x.property.2)
  have hU :
      Continuous
        (fun x : overlap ↦ U.toUpperHalfPlane (x : X)) := by
    exact (hChart g U).comp htoU
  have hV :
      Continuous
        (fun x : overlap ↦ V.toUpperHalfPlane (x : X)) := by
    exact (hChart g V).comp htoV
  exact ⟨hV, (realMobiusRepresentativeAction_continuous A).comp hU⟩

/--
%%handwave
name: Continuity of a real-Mobius comparison on a chart overlap
statement:
  Let \(U,V\) be hyperbolic local charts and \(A\) a real Mobius transformation. On \(\operatorname{dom}(U)\cap\operatorname{dom}(V)\), both \(x\mapsto V(x)\) and \(x\mapsto A(U(x))\) are continuous.
proof:
  Restrict the continuous chart maps to the overlap, and compose the restriction of \(U\) with the continuous real Mobius action.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] :
    PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem_of_chart_continuity
    hyperbolicLocalChartContinuousOnDomainTheorem

/--
Closedness target for the local-chart equality locus.

This should follow from continuity of the local chart maps and of the real
Mobius action.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        IsClosed (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet U V A)

/-- Continuity of the two compared maps makes the equality locus closed. -/
def pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem_of_continuity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hCont :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem X := by
  intro g U V A x₀ hpoint
  rcases hCont g U V A x₀ hpoint with ⟨hV, hA⟩
  simpa [pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet] using
    isClosed_eq hV hA

/--
%%handwave
name: Closedness of a real-Mobius equality locus
statement:
  For hyperbolic local charts \(U,V\) and a real Mobius transformation \(A\), the set
  \[
    \{x\in\operatorname{dom}(U)\cap\operatorname{dom}(V):V(x)=A(U(x))\}
  \]
  is closed relative to the chart overlap.
proof:
  It is the equality locus of the two continuous maps \(x\mapsto V(x)\) and \(x\mapsto A(U(x))\), hence is closed because the upper half-plane is Hausdorff.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] :
    PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem_of_continuity
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem

/--
Openness target for the local-chart equality locus.

This is the local identity-principle/local-isometry uniqueness input: a
pointed match should persist on a small neighborhood in the overlap.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        IsOpen (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet U V A)

/--
Local persistence target for a pointed real-Mobius equality of hyperbolic local
charts.

This is the pointwise identity-principle form of the openness input: if the
comparison equality holds at one point of the overlap, then it holds on a
neighborhood of that point inside the overlap.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionLocalPersistenceTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        ∀ y, y ∈ U.domain → y ∈ V.domain →
          V.toUpperHalfPlane y =
            realMobiusRepresentativeAction A (U.toUpperHalfPlane y) →
            ∃ W : Set X,
              IsOpen W ∧ y ∈ W ∧
                ∀ z, z ∈ W → z ∈ U.domain → z ∈ V.domain →
                  V.toUpperHalfPlane z =
                    realMobiusRepresentativeAction A (U.toUpperHalfPlane z)

/--
Openness target for the one-jet equality locus of a pointed comparison.

This is the mathematically natural local identity-principle target: a
holomorphic hyperbolic local isometry is locally determined by its value and
oriented first-order frame.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        IsOpen
          (pointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySet
            U V A)

/--
Openness target for the first-order frame-match locus of a pointed
real-Mobius comparison.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsOpenTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        IsOpen
          (pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet
            U V A)

/--
Closedness target for the first-order frame-match locus of a pointed
real-Mobius comparison.

Together with the already-proved closedness of the value-equality locus, this
is exactly the nontrivial closedness content of the corrected one-jet locus.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        IsClosed
          (pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet
            U V A)

/--
Closedness target for the concrete value-plus-coordinate-derivative
first-order locus.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        IsClosed
          (pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSet
            U V A)

/--
Derivative-continuity target for the concrete first-order comparison locus.

The value component of the concrete locus is already closed by continuity of
the two chart maps.  This target isolates the remaining derivative comparison.
-/
def PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ →
        Continuous
          (fun x : {x : X // x ∈ U.domain ∩ V.domain} ↦
            hyperbolicLocalChartCoordinateDerivativeAt V (x : X)) ∧
        Continuous
          (fun x : {x : X // x ∈ U.domain ∩ V.domain} ↦
            realMobiusRepresentativeDerivativeAt A
                (U.toUpperHalfPlane (x : X)) *
              hyperbolicLocalChartCoordinateDerivativeAt U (x : X))

/--
Continuity target for the ambient-coordinate derivative of a hyperbolic local
chart on its domain.
-/
def HyperbolicLocalChartCoordinateDerivativeContinuousOnDomainTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U : HyperbolicLocalChart X g),
    Continuous
      (fun x : {x : X // x ∈ U.domain} ↦
        hyperbolicLocalChartCoordinateDerivativeAt U (x : X))

/--
Chart-value continuity and chart-derivative continuity imply continuity of
the concrete first-order derivative comparison maps.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem_of_chartDerivativeContinuity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeContinuousOnDomainTheorem X) :
    PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem
      X := by
  intro g U V A x₀ _hpoint
  let overlap : Set X := U.domain ∩ V.domain
  let toUDomain : overlap → {x : X // x ∈ U.domain} :=
    fun x ↦ ⟨x, x.property.1⟩
  let toVDomain : overlap → {x : X // x ∈ V.domain} :=
    fun x ↦ ⟨x, x.property.2⟩
  have htoU : Continuous toUDomain :=
    continuous_subtype_val.subtype_mk (fun x ↦ x.property.1)
  have htoV : Continuous toVDomain :=
    continuous_subtype_val.subtype_mk (fun x ↦ x.property.2)
  have hLeft :
      Continuous
        (fun x : overlap ↦
          hyperbolicLocalChartCoordinateDerivativeAt V (x : X)) :=
    (hDeriv g V).comp htoV
  have hUValue :
      Continuous (fun x : overlap ↦ U.toUpperHalfPlane (x : X)) :=
    (hChart g U).comp htoU
  have hMobiusDeriv :
      Continuous (fun p : ℍ ↦ realMobiusRepresentativeDerivativeAt A p) := by
    simpa [realMobiusRepresentativeDerivativeAt] using
      realMobiusRepresentativeAction_deriv_continuous A
  have hMobiusOnU :
      Continuous
        (fun x : overlap ↦
          realMobiusRepresentativeDerivativeAt A
            (U.toUpperHalfPlane (x : X))) :=
    hMobiusDeriv.comp hUValue
  have hUDeriv :
      Continuous
        (fun x : overlap ↦
          hyperbolicLocalChartCoordinateDerivativeAt U (x : X)) :=
    (hDeriv g U).comp htoU
  exact ⟨hLeft, hMobiusOnU.mul hUDeriv⟩

/--
Continuity of the derivative comparison maps makes the concrete
value-plus-derivative first-order locus closed.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem_of_derivativeContinuity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderDerivativeContinuityTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
      X := by
  intro g U V A x₀ hpoint
  have hValueClosed :
      IsClosed
        (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet U V A) :=
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
      g U V A x₀ hpoint
  rcases hDeriv g U V A x₀ hpoint with ⟨hLeft, hRight⟩
  have hDerivativeClosed :
      IsClosed
        {x : {x : X // x ∈ U.domain ∩ V.domain} |
          hyperbolicLocalChartCoordinateDerivativeAt V (x : X) =
            realMobiusRepresentativeDerivativeAt A
                (U.toUpperHalfPlane (x : X)) *
              hyperbolicLocalChartCoordinateDerivativeAt U (x : X)} :=
    isClosed_eq hLeft hRight
  simpa [pointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSet,
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet,
    HyperbolicLocalChartConcreteFirstOrderMatch, Set.setOf_and] using
    hValueClosed.inter hDerivativeClosed

/--
Closedness of the concrete value-plus-derivative locus gives closedness of
the abstract first-order-frame locus, once local charts provide their pointed
coordinate-derivative data.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem_of_coordinateDerivativeData_concreteFirstOrderClosed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hData :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X)
    (hConcrete :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem
      X := by
  intro g U V A x₀ hpoint
  rw [
    pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSet_eq_concreteFirstOrderMatchSet_of_coordinateDerivativeData
      hData U V A]
  exact hConcrete g U V A x₀ hpoint

/--
The Poincare pullback squared-density formula supplies the pointed coordinate
derivative data needed to use a concrete first-order closedness theorem.
-/
def pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem_of_pullbackSquaredDensityFormula_concreteFirstOrderClosed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hConcrete :
      PointedHyperbolicLocalChartRealMobiusTransitionConcreteFirstOrderMatchSetIsClosedTheorem
        X) :
    PointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionFirstOrderMatchSetIsClosedTheorem_of_coordinateDerivativeData_concreteFirstOrderClosed
    (hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula_proved
      hPull)
    hConcrete

end HyperbolicMetric

end

end JJMath
