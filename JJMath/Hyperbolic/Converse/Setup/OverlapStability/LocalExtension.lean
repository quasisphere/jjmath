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
Abstract first-order frame matching agrees with the concrete value-plus-
coordinate-derivative condition, provided each local chart supplies pointed
coordinate-derivative data on its domain.
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
For the current pointed-frame predicate, the one-jet locus is exactly the
first-order match locus: the frame relation already remembers the equality of
base points.
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
Continuity of a coordinate pullback formula on its surface domain.

This is the elementary composition step: the surface map is the coordinate
map followed by the upper-half-plane branch.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChartContinuousOnDomain_of_coordinate_localMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g)
    (hCoordinate :
      Continuous (fun x : {x : X // x ∈ F.domain} ↦ F.coordinate (x : X)))
    (hLocalMap :
      Continuous
        (fun z : {z : ℂ // z ∈ F.coordinateDomain} ↦ F.localMap (z : ℂ))) :
    Continuous
      (fun x : {x : X //
          x ∈ F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart.domain} ↦
        F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart.toUpperHalfPlane
          (x : X)) := by
  let toCoordinateDomain :
      {x : X // x ∈ F.domain} → {z : ℂ // z ∈ F.coordinateDomain} :=
    fun x ↦ ⟨F.coordinate (x : X), F.coordinate_mem_domain (x : X) x.property⟩
  have hToCoordinateDomain : Continuous toCoordinateDomain :=
    hCoordinate.subtype_mk
      (fun x ↦ F.coordinate_mem_domain (x : X) x.property)
  simpa [CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlane,
    CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlanePullbackFormula,
    UpperHalfPlanePullbackFormula.toHyperbolicLocalChart, toCoordinateDomain] using
    hLocalMap.comp hToCoordinateDomain

/--
Domainwise coordinate continuity is enough for the same coordinate-pullback
continuity conclusion.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChartContinuousOnDomain_of_coordinateContinuousOn_localMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g)
    (hCoordinate : ContinuousOn F.coordinate F.domain)
    (hLocalMap :
      Continuous
        (fun z : {z : ℂ // z ∈ F.coordinateDomain} ↦ F.localMap (z : ℂ))) :
    Continuous
      (fun x : {x : X //
          x ∈ F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart.domain} ↦
        F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart.toUpperHalfPlane
          (x : X)) :=
  CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChartContinuousOnDomain_of_coordinate_localMap F
    (by
      simpa [Set.restrict] using
        (continuousOn_iff_continuous_restrict.mp hCoordinate))
    hLocalMap

/--
The selected surface branch coming from pointed Schwarzian predata is
continuous on its shrunk surface domain, provided the underlying formula
coordinate is continuous on its formula domain.
-/
theorem SurfaceSchwarzianPointedBranchPreData.solutionAt_hyperbolicLocalChartContinuousOnDomain_of_coordinateContinuousOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {A : LocalLiouvilleMetricFormulaAtlas X g}
    (B : SurfaceSchwarzianPointedBranchPreData A) (x : X)
    (hCoordinate :
      ContinuousOn (A.formulaAt x).coordinate (A.formulaAt x).domain) :
    Continuous
      (fun y : {y : X // y ∈ ((B.solutionAt x).toHyperbolicLocalChart).domain} ↦
        ((B.solutionAt x).toHyperbolicLocalChart).toUpperHalfPlane (y : X)) := by
  let H := B.branchAt x
  let F := B.restrictedFormulaAt x
  have hCoordinateRestricted : ContinuousOn F.coordinate F.domain := by
    have hMono : F.domain ⊆ (A.formulaAt x).domain := by
      intro y hy
      exact hy.1
    simpa [F, SurfaceSchwarzianPointedBranchPreData.restrictedFormulaAt,
      LocalLiouvilleMetricFormula.restrictDomainToCoordinateSubset] using
      hCoordinate.mono hMono
  have hLocalMap :
      Continuous
        (fun z : {z : ℂ //
            z ∈ (B.solutionAt x).pullbackFormula.coordinateDomain} ↦
          (B.solutionAt x).pullbackFormula.localMap (z : ℂ)) := by
    simpa [SurfaceSchwarzianPointedBranchPreData.solutionAt,
      LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula,
      H, F] using
      (localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem H)
  have hCoordinatePullback :
      ContinuousOn
        (B.solutionAt x).pullbackFormula.coordinate
        (B.solutionAt x).pullbackFormula.domain := by
    simpa [SurfaceSchwarzianPointedBranchPreData.solutionAt,
      LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula,
      H, F] using hCoordinateRestricted
  exact
    CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChartContinuousOnDomain_of_coordinateContinuousOn_localMap
      (B.solutionAt x).pullbackFormula hCoordinatePullback hLocalMap

/--
Charted formula coordinates give continuity of each selected pointed
Schwarzian surface branch on its shrunk domain.
-/
theorem SurfaceSchwarzianPointedBranchPreData.solutionAt_hyperbolicLocalChartContinuousOnDomain_of_coordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {A : LocalLiouvilleMetricFormulaAtlas X g}
    (B : SurfaceSchwarzianPointedBranchPreData A)
    (hChart : LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain A)
    (x : X) :
    Continuous
      (fun y : {y : X // y ∈ ((B.solutionAt x).toHyperbolicLocalChart).domain} ↦
        ((B.solutionAt x).toHyperbolicLocalChart).toUpperHalfPlane (y : X)) := by
  rcases hChart x with ⟨hSub, hEq⟩
  exact
    SurfaceSchwarzianPointedBranchPreData.solutionAt_hyperbolicLocalChartContinuousOnDomain_of_coordinateContinuousOn
      B x
      (((chartAt ℂ x).continuousOn_toFun.mono hSub).congr hEq)

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
Membership in the same-coordinate surface one-jet locus gives the pointed
real-Mobius transition for the induced surface hyperbolic charts.
-/
theorem LocalUpperHalfPlaneDevelopingMap.pointedRealMobiusTransition_of_coordinateBranchOneJetSet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    {A : RealMobiusRepresentative} {x₀ : X}
    (hEq : Set.EqOn F.coordinate (chartAt ℂ x₀) F.domain)
    (hx₀ :
      x₀ ∈ F.domain ∧ F.coordinate x₀ ∈ H₁.domain ∩ H₂.domain)
    (hmem :
      (⟨x₀, hx₀⟩ :
        {x : X // x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
          localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
            F H₁ H₂ A) :
    HyperbolicLocalChartPointedRealMobiusTransition
      (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₁).toHyperbolicLocalChart
      (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₂).toHyperbolicLocalChart
      A x₀ :=
  LocalUpperHalfPlaneDevelopingMap.pointedRealMobiusTransition_of_coordinateBranchOneJet
    H₁ H₂ hImage₁ hImage₂ hx₀.1 hEq hx₀.2
    (by
      simpa [localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet] using hmem)

/--
Membership in the same-coordinate surface one-jet locus gives the pointed
real-Mobius transition for the induced surface hyperbolic charts from local
ambient-coordinate compatibility at the point.
-/
theorem LocalUpperHalfPlaneDevelopingMap.pointedRealMobiusTransition_of_coordinateBranchOneJetSet_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    {A : RealMobiusRepresentative} {x₀ : X}
    (hCoord₁ :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₁).pullbackFormula) x₀)
    (hCoord₂ :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        ((H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).pullbackFormula) x₀)
    (hx₀ :
      x₀ ∈ F.domain ∧ F.coordinate x₀ ∈ H₁.domain ∩ H₂.domain)
    (hmem :
      (⟨x₀, hx₀⟩ :
        {x : X // x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
          localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
            F H₁ H₂ A) :
    HyperbolicLocalChartPointedRealMobiusTransition
      (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₁).toHyperbolicLocalChart
      (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₂).toHyperbolicLocalChart
      A x₀ :=
  LocalUpperHalfPlaneDevelopingMap.pointedRealMobiusTransition_of_coordinateBranchOneJet_coordinateEventuallyEq
    H₁ H₂ hImage₁ hImage₂ hx₀.1 hCoord₁ hCoord₂ hx₀.2
    (by
      simpa [localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet] using hmem)

/--
If the coordinate-branch one-jet locus is open, then its same-coordinate
surface pullback is open.
-/
theorem localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isOpen_of_coordinateContinuousOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : LocalLiouvilleMetricFormula X g)
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative)
    (hCoordinate :
      ContinuousOn F.coordinate
        {x : X | x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain})
    (hBranch :
      IsOpen (pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A)) :
    IsOpen
      (localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet F H₁ H₂ A) := by
  let D : Set X :=
    {x : X | x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain}
  let toBranchOverlap : D → {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} :=
    fun x ↦ ⟨F.coordinate (x : X), x.property.2⟩
  have hCoordinateSubtype :
      Continuous (fun x : D ↦ F.coordinate (x : X)) := by
    simpa [D, Set.restrict] using
      (continuousOn_iff_continuous_restrict.mp hCoordinate)
  have hToBranchOverlap : Continuous toBranchOverlap :=
    hCoordinateSubtype.subtype_mk (fun x ↦ x.property.2)
  simpa [localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet,
    toBranchOverlap, D] using hBranch.preimage hToBranchOverlap

/--
Chart-compatible formula coordinates make the same-coordinate surface pullback
of an open coordinate-branch one-jet locus open.
-/
theorem localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isOpen_of_coordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : LocalLiouvilleMetricFormula X g) {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain)
    (hBranch :
      IsOpen (pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A)) :
    IsOpen
      (localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet F H₁ H₂ A) := by
  let D : Set X :=
    {x : X | x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain}
  have hCoordinate : ContinuousOn F.coordinate D := by
    exact ((chartAt ℂ center).continuousOn_toFun.mono
      (fun x hx ↦ hChart.1 hx.1)).congr
        (fun x hx ↦ hChart.2 hx.1)
  exact
    localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isOpen_of_coordinateContinuousOn
      F H₁ H₂ A (by simpa [D] using hCoordinate) hBranch

/--
If the coordinate-branch one-jet locus is closed, then its same-coordinate
surface pullback is closed.
-/
theorem localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isClosed_of_coordinateContinuousOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : LocalLiouvilleMetricFormula X g)
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative)
    (hCoordinate :
      ContinuousOn F.coordinate
        {x : X | x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain})
    (hBranch :
      IsClosed (pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A)) :
    IsClosed
      (localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet F H₁ H₂ A) := by
  let D : Set X :=
    {x : X | x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain}
  let toBranchOverlap : D → {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} :=
    fun x ↦ ⟨F.coordinate (x : X), x.property.2⟩
  have hCoordinateSubtype :
      Continuous (fun x : D ↦ F.coordinate (x : X)) := by
    simpa [D, Set.restrict] using
      (continuousOn_iff_continuous_restrict.mp hCoordinate)
  have hToBranchOverlap : Continuous toBranchOverlap :=
    hCoordinateSubtype.subtype_mk (fun x ↦ x.property.2)
  simpa [localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet,
    toBranchOverlap, D] using hBranch.preimage hToBranchOverlap

/--
Chart-compatible formula coordinates make the same-coordinate surface pullback
of a closed coordinate-branch one-jet locus closed.
-/
theorem localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isClosed_of_coordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : LocalLiouvilleMetricFormula X g) {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain)
    (hBranch :
      IsClosed (pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A)) :
    IsClosed
      (localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet F H₁ H₂ A) := by
  let D : Set X :=
    {x : X | x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain}
  have hCoordinate : ContinuousOn F.coordinate D := by
    exact ((chartAt ℂ center).continuousOn_toFun.mono
      (fun x hx ↦ hChart.1 hx.1)).congr
        (fun x hx ↦ hChart.2 hx.1)
  exact
    localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isClosed_of_coordinateContinuousOn
      F H₁ H₂ A (by simpa [D] using hCoordinate) hBranch

/--
For one coordinate chart, the Schwarzian identity-principle theorem gives an
open same-coordinate surface one-jet locus.
-/
theorem localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isOpen_of_projectiveFirstSecondDerivative_scalarClosed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : LocalLiouvilleMetricFormula X g) {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (hu : F.conformalFactor.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain) :
    IsOpen
      (localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet F H₁ H₂ A) :=
  localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isOpen_of_coordinateChartedOnDomain
    F H₁ H₂ A hChart
    (pointedRealMobiusTransitionOneJetEqualitySet_isOpen_of_projectiveFirstSecondDerivative_scalarClosed
      H₁ H₂ A z₀ hu hpoint hCoeff hProjFirst hProjSecond)

/--
For one coordinate chart, projective derivative regularity makes the
same-coordinate surface one-jet locus closed.
-/
theorem localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isClosed_of_pairProjectiveDerivative_scalarClosed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : LocalLiouvilleMetricFormula X g) {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : F.conformalFactor.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain) :
    IsClosed
      (localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet F H₁ H₂ A) :=
  localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isClosed_of_coordinateChartedOnDomain
    F H₁ H₂ A hChart
    (pointedRealMobiusTransitionOneJetEqualitySet_isClosed_of_pairProjectiveDerivative
      H₁ H₂ A z₀ hu hpoint R₁ R₂)

/--
For one coordinate chart, the fixed-pair Schwarzian identity-principle theorem
gives an open same-coordinate surface one-jet locus from the two selected
branches' own projective derivative data.
-/
theorem localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isOpen_of_pairProjectiveDerivative_scalarClosed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : LocalLiouvilleMetricFormula X g) {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : F.conformalFactor.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain) :
    IsOpen
      (localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet F H₁ H₂ A) :=
  localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isOpen_of_coordinateChartedOnDomain
    F H₁ H₂ A hChart
    (pointedRealMobiusTransitionOneJetEqualitySet_isOpen_of_pairProjectiveDerivative_coefficientAgreement
      H₁ H₂ A z₀ hu hpoint R₁ R₂ hCoeff
      pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem_proved)

/--
Openness of the same-coordinate surface one-jet locus is exactly local
persistence of that one-jet comparison in the surface.
-/
theorem localLiouvilleMetricFormulaCoordinateBranchOneJetLocalPersistence_of_isOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : LocalLiouvilleMetricFormula X g)
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative)
    (hOpen :
      IsOpen
        (localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
          F H₁ H₂ A)) :
    ∀ x : X,
      (hx : x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain) →
      (⟨x, hx⟩ :
        {x : X // x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
          localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
            F H₁ H₂ A →
        ∃ W : Set X,
          IsOpen W ∧ x ∈ W ∧
            ∀ y : X,
              y ∈ W →
              (hy : y ∈ F.domain ∧ F.coordinate y ∈ H₁.domain ∩ H₂.domain) →
                (⟨y, hy⟩ :
                  {x : X // x ∈ F.domain ∧
                    F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
                  localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
                    F H₁ H₂ A := by
  intro x hx hxJet
  let D : Set X := {x : X | x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain}
  let E : Set D := localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet F H₁ H₂ A
  have hEopen : IsOpen E := hOpen
  rw [isOpen_iff_forall_mem_open] at hEopen
  rcases hEopen (⟨x, hx⟩ : D) (by simpa [E] using hxJet) with
    ⟨O, hOsub, hOopen, hxO⟩
  rcases isOpen_induced_iff.mp hOopen with ⟨W, hWopen, hWpre⟩
  refine ⟨W, hWopen, ?_, ?_⟩
  · have hxW : (⟨x, hx⟩ : D) ∈ Subtype.val ⁻¹' W := by
      rw [hWpre]
      exact hxO
    exact hxW
  · intro y hyW hy
    have hyO : (⟨y, hy⟩ : D) ∈ O := by
      have hyPre : (⟨y, hy⟩ : D) ∈ Subtype.val ⁻¹' W := hyW
      rwa [hWpre] at hyPre
    have hyE : (⟨y, hy⟩ : D) ∈ E := hOsub hyO
    simpa [E] using hyE

/--
For one coordinate chart, projective derivative regularity and the proved
Schwarzian identity-principle give local persistence of coordinate-branch
one-jet agreement in the surface.
-/
theorem localLiouvilleMetricFormulaCoordinateBranchOneJetLocalPersistence_of_pairProjectiveDerivative_scalarClosed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : LocalLiouvilleMetricFormula X g) {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : F.conformalFactor.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain) :
    ∀ x : X,
      (hx : x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain) →
      (⟨x, hx⟩ :
        {x : X // x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
          localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
            F H₁ H₂ A →
        ∃ W : Set X,
          IsOpen W ∧ x ∈ W ∧
            ∀ y : X,
              y ∈ W →
              (hy : y ∈ F.domain ∧ F.coordinate y ∈ H₁.domain ∩ H₂.domain) →
                (⟨y, hy⟩ :
                  {x : X // x ∈ F.domain ∧
                    F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
                  localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
                    F H₁ H₂ A :=
  localLiouvilleMetricFormulaCoordinateBranchOneJetLocalPersistence_of_isOpen
    F H₁ H₂ A
    (localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isOpen_of_pairProjectiveDerivative_scalarClosed
      F H₁ H₂ A z₀ R₁ R₂ hu hpoint hCoeff hChart)

/--
On a preconnected same-coordinate surface overlap, one base one-jet match
propagates to every point of the overlap.

The pointed real-Mobius branch datum used by the analytic closed/open theorems
is recovered from the base one-jet match itself; there is no separate
placeholder transition hypothesis.
-/
theorem localLiouvilleMetricFormulaCoordinateBranchOneJetExtendsOnPreconnectedOverlap_of_pairProjectiveDerivative_scalarClosed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : LocalLiouvilleMetricFormula X g) {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : F.conformalFactor.SolvesLiouvilleEquation)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain)
    (hconn :
      IsPreconnected
        {x : X | x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain})
    (x₀ : X)
    (hx₀ : x₀ ∈ F.domain ∧ F.coordinate x₀ ∈ H₁.domain ∩ H₂.domain)
    (hx₀Jet :
      (⟨x₀, hx₀⟩ :
        {x : X // x ∈ F.domain ∧
          F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
          localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
            F H₁ H₂ A) :
    ∀ x,
      (hx : x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain) →
        (⟨x, hx⟩ :
          {x : X // x ∈ F.domain ∧
            F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
          localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
            F H₁ H₂ A := by
  let D : Set X :=
    {x : X | x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain}
  let E : Set D := localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet F H₁ H₂ A
  have hx₀BranchJet :
      H₂.upperHalfPlaneMap (F.coordinate x₀) =
          realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap (F.coordinate x₀)) ∧
        deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (F.coordinate x₀) =
          deriv
            (fun w : ℂ ↦
              (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
            (F.coordinate x₀) := by
    simpa [localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet] using hx₀Jet
  have hpoint :
      H₁.HasPointedRealMobiusTransition H₂ A (F.coordinate x₀) :=
    ⟨hx₀.2.1, hx₀.2.2, hx₀BranchJet.1, hx₀BranchJet.2⟩
  have hClosed : IsClosed E := by
    simpa [E] using
      (localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isClosed_of_pairProjectiveDerivative_scalarClosed
        F H₁ H₂ A (F.coordinate x₀) R₁ R₂ hu hpoint hChart)
  have hOpen : IsOpen E := by
    simpa [E] using
      (localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet_isOpen_of_pairProjectiveDerivative_scalarClosed
        F H₁ H₂ A (F.coordinate x₀) R₁ R₂ hu hpoint hCoeff hChart)
  haveI : PreconnectedSpace D := Subtype.preconnectedSpace (by simpa [D] using hconn)
  have hE : IsClopen E := ⟨hClosed, hOpen⟩
  have hx₀E : (⟨x₀, hx₀⟩ : D) ∈ E := by
    simpa [D, E] using hx₀Jet
  have hE_univ : E = Set.univ :=
    IsClopen.eq_univ hE ⟨⟨x₀, hx₀⟩, hx₀E⟩
  intro x hx
  have hxE : (⟨x, hx⟩ : D) ∈ E := by
    rw [hE_univ]
    exact Set.mem_univ _
  simpa [D, E] using hxE

/--
Same-coordinate surface one-jet persistence gives persistence of the
corresponding value equality and abstract oriented first-order-frame match for
the induced hyperbolic local charts.

The additional chart-identification hypothesis is the precise surface
boundary: at each nearby point the formula coordinate must agree with the
ambient chart used to read off the abstract tangent frame.
-/
theorem LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetLocalPersistence_of_coordinateBranchOneJetLocalPersistence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    (A : RealMobiusRepresentative)
    (hChartAt :
      ∀ y, y ∈ F.domain → Set.EqOn F.coordinate (chartAt ℂ y) F.domain)
    (hLocal :
      ∀ x : X,
        (hx : x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain) →
        (⟨x, hx⟩ :
          {x : X // x ∈ F.domain ∧
            F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
            localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
              F H₁ H₂ A →
          ∃ W : Set X,
            IsOpen W ∧ x ∈ W ∧
              ∀ y : X,
                y ∈ W →
                (hy : y ∈ F.domain ∧ F.coordinate y ∈ H₁.domain ∩ H₂.domain) →
                  (⟨y, hy⟩ :
                    {x : X // x ∈ F.domain ∧
                      F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
                    localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
                      F H₁ H₂ A)
    (x : X)
    (hx : x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain)
    (hxJet :
      (⟨x, hx⟩ :
        {x : X // x ∈ F.domain ∧
          F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
          localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
            F H₁ H₂ A) :
    ∃ W : Set X,
      IsOpen W ∧ x ∈ W ∧
        ∀ y, y ∈ W →
          y ∈
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart.domain →
          y ∈
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.domain →
            (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.toUpperHalfPlane y =
              realMobiusRepresentativeAction A
                ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                  hImage₁).toHyperbolicLocalChart.toUpperHalfPlane y) ∧
            HyperbolicLocalChartPointedFirstOrderMatch
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart A y := by
  rcases hLocal x hx hxJet with ⟨W, hWopen, hxW, hW⟩
  refine ⟨W, hWopen, hxW, ?_⟩
  intro y hyW hyU hyV
  have hyF : y ∈ F.domain := by
    simpa [LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula,
      LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart,
      UpperHalfPlanePullbackFormula.toHyperbolicLocalChart] using hyU
  have hy :
      y ∈ F.domain ∧ F.coordinate y ∈ H₁.domain ∩ H₂.domain :=
    ⟨hyF, hImage₁ y hyF, hImage₂ y hyF⟩
  have hyJet := hW y hyW hy
  have hPoint :
      HyperbolicLocalChartPointedRealMobiusTransition
        (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₁).toHyperbolicLocalChart
        (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart A y :=
    LocalUpperHalfPlaneDevelopingMap.pointedRealMobiusTransition_of_coordinateBranchOneJetSet
      H₁ H₂ hImage₁ hImage₂ (A := A) (x₀ := y)
      (hChartAt y hyF) hy hyJet
  exact ⟨hPoint.value_match, hPoint.first_order_match⟩

/--
Same-coordinate surface one-jet persistence gives persistence of the
corresponding value equality and abstract oriented first-order-frame match
from local ambient-coordinate compatibility at each nearby point.
-/
theorem LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetLocalPersistence_of_coordinateBranchOneJetLocalPersistence_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    (A : RealMobiusRepresentative)
    (hCoordAt :
      ∀ y,
        (hy : y ∈ F.domain ∧ F.coordinate y ∈ H₁.domain ∩ H₂.domain) →
          CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
            ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₁).pullbackFormula) y ∧
          CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
            ((H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₂).pullbackFormula) y)
    (hLocal :
      ∀ x : X,
        (hx : x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain) →
        (⟨x, hx⟩ :
          {x : X // x ∈ F.domain ∧
            F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
            localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
              F H₁ H₂ A →
          ∃ W : Set X,
            IsOpen W ∧ x ∈ W ∧
              ∀ y : X,
                y ∈ W →
                (hy : y ∈ F.domain ∧ F.coordinate y ∈ H₁.domain ∩ H₂.domain) →
                  (⟨y, hy⟩ :
                    {x : X // x ∈ F.domain ∧
                      F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
                    localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
                      F H₁ H₂ A)
    (x : X)
    (hx : x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain)
    (hxJet :
      (⟨x, hx⟩ :
        {x : X // x ∈ F.domain ∧
          F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
          localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
            F H₁ H₂ A) :
    ∃ W : Set X,
      IsOpen W ∧ x ∈ W ∧
        ∀ y, y ∈ W →
          y ∈
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart.domain →
          y ∈
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.domain →
            (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.toUpperHalfPlane y =
              realMobiusRepresentativeAction A
                ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                  hImage₁).toHyperbolicLocalChart.toUpperHalfPlane y) ∧
            HyperbolicLocalChartPointedFirstOrderMatch
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart A y := by
  rcases hLocal x hx hxJet with ⟨W, hWopen, hxW, hW⟩
  refine ⟨W, hWopen, hxW, ?_⟩
  intro y hyW hyU hyV
  have hyF : y ∈ F.domain := by
    simpa [LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula,
      LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart,
      UpperHalfPlanePullbackFormula.toHyperbolicLocalChart] using hyU
  have hy :
      y ∈ F.domain ∧ F.coordinate y ∈ H₁.domain ∩ H₂.domain :=
    ⟨hyF, hImage₁ y hyF, hImage₂ y hyF⟩
  have hyJet := hW y hyW hy
  rcases hCoordAt y hy with ⟨hCoord₁, hCoord₂⟩
  have hPoint :
      HyperbolicLocalChartPointedRealMobiusTransition
        (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₁).toHyperbolicLocalChart
        (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart A y :=
    LocalUpperHalfPlaneDevelopingMap.pointedRealMobiusTransition_of_coordinateBranchOneJetSet_coordinateEventuallyEq
      H₁ H₂ hImage₁ hImage₂ (A := A) (x₀ := y)
      hCoord₁ hCoord₂ hy hyJet
  exact ⟨hPoint.value_match, hPoint.first_order_match⟩

/--
The proved Schwarzian identity-principle package gives the same-coordinate
surface local uniqueness statement for the induced hyperbolic local charts,
provided formula coordinates agree with the ambient charts at the nearby
points where the abstract tangent frames are read.
-/
theorem LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetLocalPersistence_of_pairProjectiveDerivative_scalarClosed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : F.conformalFactor.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain)
    (hChartAt :
      ∀ y, y ∈ F.domain → Set.EqOn F.coordinate (chartAt ℂ y) F.domain)
    (x : X)
    (hx : x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain)
    (hxJet :
      (⟨x, hx⟩ :
        {x : X // x ∈ F.domain ∧
          F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
          localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
            F H₁ H₂ A) :
    ∃ W : Set X,
      IsOpen W ∧ x ∈ W ∧
        ∀ y, y ∈ W →
          y ∈
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart.domain →
          y ∈
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.domain →
            (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.toUpperHalfPlane y =
              realMobiusRepresentativeAction A
                ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                  hImage₁).toHyperbolicLocalChart.toUpperHalfPlane y) ∧
            HyperbolicLocalChartPointedFirstOrderMatch
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart A y :=
  LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetLocalPersistence_of_coordinateBranchOneJetLocalPersistence
    H₁ H₂ hImage₁ hImage₂ A hChartAt
    (localLiouvilleMetricFormulaCoordinateBranchOneJetLocalPersistence_of_pairProjectiveDerivative_scalarClosed
      F H₁ H₂ A z₀ R₁ R₂ hu hpoint hCoeff hChart)
    x hx hxJet

/--
The proved Schwarzian identity-principle package gives the same-coordinate
surface local uniqueness statement from local ambient-coordinate compatibility
at the nearby points where the abstract tangent frames are read.
-/
theorem LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetLocalPersistence_of_pairProjectiveDerivative_scalarClosed_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : F.conformalFactor.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain)
    (hCoordAt :
      ∀ y,
        (hy : y ∈ F.domain ∧ F.coordinate y ∈ H₁.domain ∩ H₂.domain) →
          CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
            ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₁).pullbackFormula) y ∧
          CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
            ((H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₂).pullbackFormula) y)
    (x : X)
    (hx : x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain)
    (hxJet :
      (⟨x, hx⟩ :
        {x : X // x ∈ F.domain ∧
          F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
          localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
            F H₁ H₂ A) :
    ∃ W : Set X,
      IsOpen W ∧ x ∈ W ∧
        ∀ y, y ∈ W →
          y ∈
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart.domain →
          y ∈
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.domain →
            (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.toUpperHalfPlane y =
              realMobiusRepresentativeAction A
                ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                  hImage₁).toHyperbolicLocalChart.toUpperHalfPlane y) ∧
            HyperbolicLocalChartPointedFirstOrderMatch
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart A y :=
  LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetLocalPersistence_of_coordinateBranchOneJetLocalPersistence_coordinateEventuallyEq
    H₁ H₂ hImage₁ hImage₂ A hCoordAt
    (localLiouvilleMetricFormulaCoordinateBranchOneJetLocalPersistence_of_pairProjectiveDerivative_scalarClosed
      F H₁ H₂ A z₀ R₁ R₂ hu hpoint hCoeff hChart)
    x hx hxJet

/--
Same-coordinate local uniqueness in concrete oriented-frame form.

If, at a surface point, the two induced upper-half-plane branches have the
same value after the real Mobius postcomposition and their concrete complex
derivatives agree, then the Schwarzian identity-principle gives a surface-open
neighborhood on which value agreement and the abstract oriented-frame match
hold for the induced hyperbolic local charts.
-/
theorem LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetLocalPersistence_of_pairProjectiveDerivative_scalarClosed_and_coordinateDerivative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : F.conformalFactor.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain)
    (hChartAt :
      ∀ y, y ∈ F.domain → Set.EqOn F.coordinate (chartAt ℂ y) F.domain)
    (x : X)
    (hx : x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain)
    (hxValue :
      H₂.upperHalfPlaneMap (F.coordinate x) =
        realMobiusRepresentativeAction A
          (H₁.upperHalfPlaneMap (F.coordinate x)))
    (hxDeriv :
      deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (F.coordinate x) =
        deriv
          (fun w : ℂ ↦
            (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
          (F.coordinate x)) :
    ∃ W : Set X,
      IsOpen W ∧ x ∈ W ∧
        ∀ y, y ∈ W →
          y ∈
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart.domain →
          y ∈
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.domain →
            (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.toUpperHalfPlane y =
              realMobiusRepresentativeAction A
                ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                  hImage₁).toHyperbolicLocalChart.toUpperHalfPlane y) ∧
            HyperbolicLocalChartPointedFirstOrderMatch
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart A y := by
  have hxJet :
      (⟨x, hx⟩ :
        {x : X // x ∈ F.domain ∧
          F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
          localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
            F H₁ H₂ A := by
    exact ⟨hxValue, hxDeriv⟩
  exact
    LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetLocalPersistence_of_pairProjectiveDerivative_scalarClosed
      H₁ H₂ hImage₁ hImage₂ A z₀ R₁ R₂ hu hpoint hCoeff hChart hChartAt
      x hx hxJet

/--
For constructed upper-half-plane branches, abstract pointed-frame agreement of
the induced hyperbolic local charts is exactly the coordinate one-jet equality
used by the Schwarzian branch uniqueness theorem.

The only surface input is that the formula coordinate agrees with the ambient
chart at the point where the local-chart derivative is read.
-/
theorem LocalUpperHalfPlaneDevelopingMap.abstractFrameToCoordinateOneJet_of_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    (A : RealMobiusRepresentative)
    (hChartAt :
      ∀ y, y ∈ F.domain → Set.EqOn F.coordinate (chartAt ℂ y) F.domain)
    (y : X)
    (hy : y ∈ F.domain ∧ F.coordinate y ∈ H₁.domain ∩ H₂.domain)
    (hyValue :
      (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart.toUpperHalfPlane y =
        realMobiusRepresentativeAction A
          ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₁).toHyperbolicLocalChart.toUpperHalfPlane y))
    (hyFirst :
      HyperbolicLocalChartPointedFirstOrderMatch
        (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₁).toHyperbolicLocalChart
        (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart A y) :
    (⟨y, hy⟩ :
      {x : X // x ∈ F.domain ∧
        F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
      localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
        F H₁ H₂ A := by
  let P₁ :=
    (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₁).pullbackFormula
  let P₂ :=
    (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₂).pullbackFormula
  have hyP₁ : y ∈ P₁.domain := by
    simpa [P₁,
      LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula]
      using hy.1
  have hyP₂ : y ∈ P₂.domain := by
    simpa [P₂,
      LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula]
      using hy.1
  have hEqP₁ : Set.EqOn P₁.coordinate (chartAt ℂ y) P₁.domain := by
    simpa [P₁,
      LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula]
      using hChartAt y hy.1
  have hEqP₂ : Set.EqOn P₂.coordinate (chartAt ℂ y) P₂.domain := by
    simpa [P₂,
      LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula]
      using hChartAt y hy.1
  have hP₁Deriv :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt P₁ y :=
    CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_eqOn_chartAt
      P₁ hyP₁ hEqP₁
  have hP₂Deriv :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt P₂ y :=
    CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_eqOn_chartAt
      P₂ hyP₂ hEqP₂
  have hValue :
      H₂.upperHalfPlaneMap (F.coordinate y) =
        realMobiusRepresentativeAction A
          (H₁.upperHalfPlaneMap (F.coordinate y)) := by
    simpa [P₁, P₂,
      LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula,
      CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlane,
      CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlanePullbackFormula,
      UpperHalfPlanePullbackFormula.toHyperbolicLocalChart] using hyValue
  have hConcrete := hyFirst.concreteFirstOrderMatch
  have hDerivMul :
      deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (F.coordinate y) =
        realMobiusRepresentativeDerivativeAt A
            (H₁.upperHalfPlaneMap (F.coordinate y)) *
          deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ))
            (F.coordinate y) := by
    have hConcreteP :
        HyperbolicLocalChartConcreteFirstOrderMatch
          P₁.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart
          P₂.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart A y := by
      simpa [P₁, P₂,
        LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart] using hConcrete
    dsimp [HyperbolicLocalChartConcreteFirstOrderMatch] at hConcreteP
    dsimp [CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt] at hP₁Deriv hP₂Deriv
    rw [hP₂Deriv, hP₁Deriv] at hConcreteP
    simpa [P₁, P₂,
      LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula,
      CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlane,
      CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlanePullbackFormula,
      UpperHalfPlanePullbackFormula.toHyperbolicLocalChart] using hConcreteP
  have hChain :=
    realMobiusBranchPostcompositionDerivativeChainRuleTheorem H₁ A hy.2.1
  have hDeriv :
      deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (F.coordinate y) =
        deriv
          (fun w : ℂ ↦
            (realMobiusRepresentativeAction A
              (H₁.upperHalfPlaneMap w) : ℂ))
          (F.coordinate y) :=
    hDerivMul.trans hChain.symm
  exact ⟨hValue, hDeriv⟩

/--
For constructed upper-half-plane branches, abstract pointed-frame agreement
implies the coordinate one-jet equality from local ambient-coordinate
compatibility at the point.
-/
theorem LocalUpperHalfPlaneDevelopingMap.abstractFrameToCoordinateOneJet_of_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    (A : RealMobiusRepresentative)
    (y : X)
    (hy : y ∈ F.domain ∧ F.coordinate y ∈ H₁.domain ∩ H₂.domain)
    (hCoord₁ :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₁).pullbackFormula) y)
    (hCoord₂ :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        ((H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).pullbackFormula) y)
    (hyValue :
      (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart.toUpperHalfPlane y =
        realMobiusRepresentativeAction A
          ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₁).toHyperbolicLocalChart.toUpperHalfPlane y))
    (hyFirst :
      HyperbolicLocalChartPointedFirstOrderMatch
        (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₁).toHyperbolicLocalChart
        (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart A y) :
    (⟨y, hy⟩ :
      {x : X // x ∈ F.domain ∧
        F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
      localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
        F H₁ H₂ A := by
  let P₁ :=
    (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₁).pullbackFormula
  let P₂ :=
    (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₂).pullbackFormula
  have hP₁Deriv :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt P₁ y :=
    CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_coordinateEventuallyEq
      P₁ (by simpa [P₁] using hCoord₁)
  have hP₂Deriv :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt P₂ y :=
    CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_coordinateEventuallyEq
      P₂ (by simpa [P₂] using hCoord₂)
  have hValue :
      H₂.upperHalfPlaneMap (F.coordinate y) =
        realMobiusRepresentativeAction A
          (H₁.upperHalfPlaneMap (F.coordinate y)) := by
    simpa [P₁, P₂,
      LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula,
      CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlane,
      CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlanePullbackFormula,
      UpperHalfPlanePullbackFormula.toHyperbolicLocalChart] using hyValue
  have hConcrete := hyFirst.concreteFirstOrderMatch
  have hDerivMul :
      deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (F.coordinate y) =
        realMobiusRepresentativeDerivativeAt A
            (H₁.upperHalfPlaneMap (F.coordinate y)) *
          deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ))
            (F.coordinate y) := by
    have hConcreteP :
        HyperbolicLocalChartConcreteFirstOrderMatch
          P₁.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart
          P₂.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart A y := by
      simpa [P₁, P₂,
        LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart] using hConcrete
    dsimp [HyperbolicLocalChartConcreteFirstOrderMatch] at hConcreteP
    dsimp [CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt] at hP₁Deriv hP₂Deriv
    rw [hP₂Deriv, hP₁Deriv] at hConcreteP
    simpa [P₁, P₂,
      LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula,
      CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlane,
      CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlanePullbackFormula,
      UpperHalfPlanePullbackFormula.toHyperbolicLocalChart] using hConcreteP
  have hChain :=
    realMobiusBranchPostcompositionDerivativeChainRuleTheorem H₁ A hy.2.1
  have hDeriv :
      deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (F.coordinate y) =
        deriv
          (fun w : ℂ ↦
            (realMobiusRepresentativeAction A
              (H₁.upperHalfPlaneMap w) : ℂ))
          (F.coordinate y) :=
    hDerivMul.trans hChain.symm
  exact ⟨hValue, hDeriv⟩

/--
Same-coordinate local uniqueness in abstract oriented-frame form from local
ambient-coordinate compatibility at the points where frames are read.
-/
theorem LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetLocalPersistence_of_pairProjectiveDerivative_scalarClosed_and_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : F.conformalFactor.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain)
    (hCoordAt :
      ∀ y,
        (hy : y ∈ F.domain ∧ F.coordinate y ∈ H₁.domain ∩ H₂.domain) →
          CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
            ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₁).pullbackFormula) y ∧
          CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
            ((H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₂).pullbackFormula) y)
    (x : X)
    (hx : x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain)
    (hxValue :
      (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart.toUpperHalfPlane x =
        realMobiusRepresentativeAction A
          ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₁).toHyperbolicLocalChart.toUpperHalfPlane x))
    (hxFirst :
      HyperbolicLocalChartPointedFirstOrderMatch
        (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₁).toHyperbolicLocalChart
        (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart A x) :
    ∃ W : Set X,
      IsOpen W ∧ x ∈ W ∧
        ∀ y, y ∈ W →
          y ∈
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart.domain →
          y ∈
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.domain →
            (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.toUpperHalfPlane y =
              realMobiusRepresentativeAction A
                ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                  hImage₁).toHyperbolicLocalChart.toUpperHalfPlane y) ∧
            HyperbolicLocalChartPointedFirstOrderMatch
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart A y := by
  rcases hCoordAt x hx with ⟨hCoord₁, hCoord₂⟩
  have hxJet :
      (⟨x, hx⟩ :
        {x : X // x ∈ F.domain ∧
          F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
          localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
            F H₁ H₂ A :=
    LocalUpperHalfPlaneDevelopingMap.abstractFrameToCoordinateOneJet_of_coordinateEventuallyEq
      H₁ H₂ hImage₁ hImage₂ A x hx hCoord₁ hCoord₂ hxValue hxFirst
  exact
    LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetLocalPersistence_of_pairProjectiveDerivative_scalarClosed_coordinateEventuallyEq
      H₁ H₂ hImage₁ hImage₂ A z₀ R₁ R₂ hu hpoint hCoeff hChart
      hCoordAt x hx hxJet

/--
Abstract-frame version of the same-coordinate local uniqueness theorem.

It reduces the desired statement, phrased using
`HyperbolicLocalChartPointedFirstOrderMatch`, to the remaining identification
that the abstract oriented-frame match for these constructed charts implies
the concrete coordinate one-jet equality used by the Schwarzian identity
principle.
-/
theorem LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetLocalPersistence_of_pairProjectiveDerivative_scalarClosed_and_abstractFrameToCoordinateOneJet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : F.conformalFactor.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain)
    (hChartAt :
      ∀ y, y ∈ F.domain → Set.EqOn F.coordinate (chartAt ℂ y) F.domain)
    (hFrameToCoordinate :
      ∀ y,
        (hy : y ∈ F.domain ∧ F.coordinate y ∈ H₁.domain ∩ H₂.domain) →
          (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₂).toHyperbolicLocalChart.toUpperHalfPlane y =
            realMobiusRepresentativeAction A
              ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart.toUpperHalfPlane y) →
          HyperbolicLocalChartPointedFirstOrderMatch
            (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₁).toHyperbolicLocalChart
            (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₂).toHyperbolicLocalChart A y →
          (⟨y, hy⟩ :
            {x : X // x ∈ F.domain ∧
              F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
            localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
              F H₁ H₂ A)
    (x : X)
    (hx : x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain)
    (hxValue :
      (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart.toUpperHalfPlane x =
        realMobiusRepresentativeAction A
          ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₁).toHyperbolicLocalChart.toUpperHalfPlane x))
    (hxFirst :
      HyperbolicLocalChartPointedFirstOrderMatch
        (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₁).toHyperbolicLocalChart
        (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart A x) :
    ∃ W : Set X,
      IsOpen W ∧ x ∈ W ∧
        ∀ y, y ∈ W →
          y ∈
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart.domain →
          y ∈
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.domain →
            (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.toUpperHalfPlane y =
              realMobiusRepresentativeAction A
                ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                  hImage₁).toHyperbolicLocalChart.toUpperHalfPlane y) ∧
            HyperbolicLocalChartPointedFirstOrderMatch
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart A y :=
  LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetLocalPersistence_of_pairProjectiveDerivative_scalarClosed
    H₁ H₂ hImage₁ hImage₂ A z₀ R₁ R₂ hu hpoint hCoeff hChart hChartAt
    x hx (hFrameToCoordinate x hx hxValue hxFirst)

/--
Same-coordinate local uniqueness in abstract oriented-frame form for the
actual branches constructed from a Liouville formula.

This is the non-placeholder version of
`..._and_abstractFrameToCoordinateOneJet`: the frame-to-coordinate bridge is
proved from chart compatibility with `chartAt` at the point.
-/
theorem LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetLocalPersistence_of_pairProjectiveDerivative_scalarClosed_and_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : F.conformalFactor.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain)
    (hChartAt :
      ∀ y, y ∈ F.domain → Set.EqOn F.coordinate (chartAt ℂ y) F.domain)
    (x : X)
    (hx : x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain)
    (hxValue :
      (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart.toUpperHalfPlane x =
        realMobiusRepresentativeAction A
          ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₁).toHyperbolicLocalChart.toUpperHalfPlane x))
    (hxFirst :
      HyperbolicLocalChartPointedFirstOrderMatch
        (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₁).toHyperbolicLocalChart
        (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart A x) :
    ∃ W : Set X,
      IsOpen W ∧ x ∈ W ∧
        ∀ y, y ∈ W →
          y ∈
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart.domain →
          y ∈
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.domain →
            (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart.toUpperHalfPlane y =
              realMobiusRepresentativeAction A
                ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                  hImage₁).toHyperbolicLocalChart.toUpperHalfPlane y) ∧
            HyperbolicLocalChartPointedFirstOrderMatch
              (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₁).toHyperbolicLocalChart
              (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
                hImage₂).toHyperbolicLocalChart A y :=
  LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetLocalPersistence_of_pairProjectiveDerivative_scalarClosed_and_abstractFrameToCoordinateOneJet
    H₁ H₂ hImage₁ hImage₂ A z₀ R₁ R₂ hu hpoint hCoeff hChart hChartAt
    (fun y hy hyValue hyFirst =>
      LocalUpperHalfPlaneDevelopingMap.abstractFrameToCoordinateOneJet_of_eqOn_chartAt
        H₁ H₂ hImage₁ hImage₂ A hChartAt y hy hyValue hyFirst)
    x hx hxValue hxFirst

/--
Same-coordinate preconnected-overlap propagation in abstract oriented-frame
form from local ambient-coordinate compatibility at the points where frames
are read.

The proof is the clopen coordinate one-jet propagation lemma followed by the
already-proved conversion between coordinate one-jets and pointed
hyperbolic-chart transitions.
-/
theorem LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetExtendsOnPreconnectedOverlap_of_pairProjectiveDerivative_scalarClosed_and_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    (A : RealMobiusRepresentative)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : F.conformalFactor.SolvesLiouvilleEquation)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain)
    (hCoordAt :
      ∀ y,
        (hy : y ∈ F.domain ∧ F.coordinate y ∈ H₁.domain ∩ H₂.domain) →
          CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
            ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₁).pullbackFormula) y ∧
          CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
            ((H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₂).pullbackFormula) y)
    (hconn :
      IsPreconnected
        {x : X | x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain})
    (x₀ : X)
    (hpoint :
      HyperbolicLocalChartPointedRealMobiusTransition
        (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₁).toHyperbolicLocalChart
        (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart A x₀) :
    ∀ x,
      x ∈
          (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₁).toHyperbolicLocalChart.domain →
      x ∈
          (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₂).toHyperbolicLocalChart.domain →
        (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₂).toHyperbolicLocalChart.toUpperHalfPlane x =
          realMobiusRepresentativeAction A
            ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₁).toHyperbolicLocalChart.toUpperHalfPlane x) ∧
        HyperbolicLocalChartPointedFirstOrderMatch
          (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₁).toHyperbolicLocalChart
          (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₂).toHyperbolicLocalChart A x := by
  have hx₀F : x₀ ∈ F.domain := by
    simpa [LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula,
      LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart,
      UpperHalfPlanePullbackFormula.toHyperbolicLocalChart] using hpoint.mem_left
  have hx₀ :
      x₀ ∈ F.domain ∧ F.coordinate x₀ ∈ H₁.domain ∩ H₂.domain :=
    ⟨hx₀F, hImage₁ x₀ hx₀F, hImage₂ x₀ hx₀F⟩
  rcases hCoordAt x₀ hx₀ with ⟨hCoord₁, hCoord₂⟩
  have hx₀Jet :
      (⟨x₀, hx₀⟩ :
        {x : X // x ∈ F.domain ∧
          F.coordinate x ∈ H₁.domain ∩ H₂.domain}) ∈
          localLiouvilleMetricFormulaCoordinateBranchOneJetEqualitySet
            F H₁ H₂ A :=
    LocalUpperHalfPlaneDevelopingMap.abstractFrameToCoordinateOneJet_of_coordinateEventuallyEq
      H₁ H₂ hImage₁ hImage₂ A x₀ hx₀ hCoord₁ hCoord₂
      hpoint.value_match hpoint.first_order_match
  have hExtend :=
    localLiouvilleMetricFormulaCoordinateBranchOneJetExtendsOnPreconnectedOverlap_of_pairProjectiveDerivative_scalarClosed
      F H₁ H₂ A R₁ R₂ hu hCoeff hChart hconn x₀ hx₀ hx₀Jet
  intro x hxU hxV
  have hxF : x ∈ F.domain := by
    simpa [LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula,
      LocalLiouvilleDevelopingSolution.toHyperbolicLocalChart,
      UpperHalfPlanePullbackFormula.toHyperbolicLocalChart] using hxU
  have hx :
      x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain :=
    ⟨hxF, hImage₁ x hxF, hImage₂ x hxF⟩
  have hxJet := hExtend x hx
  rcases hCoordAt x hx with ⟨hCoord₁, hCoord₂⟩
  have hPoint :
      HyperbolicLocalChartPointedRealMobiusTransition
        (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₁).toHyperbolicLocalChart
        (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart A x :=
    LocalUpperHalfPlaneDevelopingMap.pointedRealMobiusTransition_of_coordinateBranchOneJetSet_coordinateEventuallyEq
      H₁ H₂ hImage₁ hImage₂ (A := A) (x₀ := x)
      hCoord₁ hCoord₂ hx hxJet
  exact ⟨hPoint.value_match, hPoint.first_order_match⟩

/--
Same-coordinate preconnected-overlap propagation in abstract oriented-frame
form when the formula coordinate agrees with the ambient `chartAt` coordinate
throughout the formula domain.
-/
theorem LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetExtendsOnPreconnectedOverlap_of_pairProjectiveDerivative_scalarClosed_and_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {center : X}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    (A : RealMobiusRepresentative)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : F.conformalFactor.SolvesLiouvilleEquation)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hChart :
      F.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn F.coordinate (chartAt ℂ center) F.domain)
    (hChartAt :
      ∀ y, y ∈ F.domain → Set.EqOn F.coordinate (chartAt ℂ y) F.domain)
    (hconn :
      IsPreconnected
        {x : X | x ∈ F.domain ∧ F.coordinate x ∈ H₁.domain ∩ H₂.domain})
    (x₀ : X)
    (hpoint :
      HyperbolicLocalChartPointedRealMobiusTransition
        (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₁).toHyperbolicLocalChart
        (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).toHyperbolicLocalChart A x₀) :
    ∀ x,
      x ∈
          (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₁).toHyperbolicLocalChart.domain →
      x ∈
          (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₂).toHyperbolicLocalChart.domain →
        (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₂).toHyperbolicLocalChart.toUpperHalfPlane x =
          realMobiusRepresentativeAction A
            ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₁).toHyperbolicLocalChart.toUpperHalfPlane x) ∧
        HyperbolicLocalChartPointedFirstOrderMatch
          (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₁).toHyperbolicLocalChart
          (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₂).toHyperbolicLocalChart A x := by
  have hCoordAt :
      ∀ y,
        (hy : y ∈ F.domain ∧ F.coordinate y ∈ H₁.domain ∩ H₂.domain) →
          CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
            ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₁).pullbackFormula) y ∧
          CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
            ((H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
              hImage₂).pullbackFormula) y := by
    intro y hy
    have hP₁ :
        CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
          ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₁).pullbackFormula) y := by
      exact
        CoordinateUpperHalfPlanePullbackFormula.ambientCoordinateEventuallyEqAt_of_eqOn_chartAt
          ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₁).pullbackFormula) (x₀ := y)
          (by
            simpa [LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula]
              using hy.1)
          (by
            simpa [LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula]
              using hChartAt y hy.1)
    have hP₂ :
        CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
          ((H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₂).pullbackFormula) y := by
      exact
        CoordinateUpperHalfPlanePullbackFormula.ambientCoordinateEventuallyEqAt_of_eqOn_chartAt
          ((H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
            hImage₂).pullbackFormula) (x₀ := y)
          (by
            simpa [LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula]
              using hy.1)
          (by
            simpa [LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula]
              using hChartAt y hy.1)
    exact ⟨hP₁, hP₂⟩
  exact
    LocalUpperHalfPlaneDevelopingMap.hyperbolicLocalChartOneJetExtendsOnPreconnectedOverlap_of_pairProjectiveDerivative_scalarClosed_and_coordinateEventuallyEq
      H₁ H₂ hImage₁ hImage₂ A R₁ R₂ hu hCoeff hChart hCoordAt hconn x₀ hpoint

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
Continuity of a hyperbolic local chart follows from its stored coordinate
description: the coordinate is a chart map on the surface domain and the
upper-half-plane coordinate expression is holomorphic there.
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
The maps compared in a local-chart real-Mobius equality locus are continuous.
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

/-- Local-chart real-Mobius equality loci are closed in the overlap. -/
theorem pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] :
    PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem
      X :=
  pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsClosedTheorem_of_continuity
    pointedHyperbolicLocalChartRealMobiusTransitionEqualitySetContinuityTheorem

/--
Pairwise chart-domain continuity is enough to make one local-chart
real-Mobius equality locus closed.
-/
theorem pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet_isClosed_of_chart_continuity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative)
    (hU :
      Continuous (fun x : {x : X // x ∈ U.domain} ↦
        U.toUpperHalfPlane (x : X)))
    (hV :
      Continuous (fun x : {x : X // x ∈ V.domain} ↦
        V.toUpperHalfPlane (x : X))) :
    IsClosed
      (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet U V A) := by
  let overlap : Set X := U.domain ∩ V.domain
  let toUDomain : overlap → {x : X // x ∈ U.domain} :=
    fun x ↦ ⟨x, x.property.1⟩
  let toVDomain : overlap → {x : X // x ∈ V.domain} :=
    fun x ↦ ⟨x, x.property.2⟩
  have htoU : Continuous toUDomain :=
    continuous_subtype_val.subtype_mk (fun x ↦ x.property.1)
  have htoV : Continuous toVDomain :=
    continuous_subtype_val.subtype_mk (fun x ↦ x.property.2)
  have hUoverlap :
      Continuous (fun x : overlap ↦ U.toUpperHalfPlane (x : X)) :=
    hU.comp htoU
  have hVoverlap :
      Continuous (fun x : overlap ↦ V.toUpperHalfPlane (x : X)) :=
    hV.comp htoV
  simpa [pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet, overlap] using
    isClosed_eq hVoverlap
      ((realMobiusRepresentativeAction_continuous A).comp hUoverlap)

/--
For selected pointed Schwarzian surface branches with charted formula
coordinates, the pointed equality locus is closed.
-/
theorem SurfaceSchwarzianPointedBranchPreData.pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet_isClosed_of_coordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {A : LocalLiouvilleMetricFormulaAtlas X g}
    (B : SurfaceSchwarzianPointedBranchPreData A)
    (hChart : LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain A)
    (x y : X) (M : RealMobiusRepresentative) :
    IsClosed
      (pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet
        ((B.solutionAt x).toHyperbolicLocalChart)
        ((B.solutionAt y).toHyperbolicLocalChart) M) :=
  pointedHyperbolicLocalChartRealMobiusTransitionEqualitySet_isClosed_of_chart_continuity
    ((B.solutionAt x).toHyperbolicLocalChart)
    ((B.solutionAt y).toHyperbolicLocalChart) M
    (SurfaceSchwarzianPointedBranchPreData.solutionAt_hyperbolicLocalChartContinuousOnDomain_of_coordinateChartedOnDomain
      B hChart x)
    (SurfaceSchwarzianPointedBranchPreData.solutionAt_hyperbolicLocalChartContinuousOnDomain_of_coordinateChartedOnDomain
      B hChart y)

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
