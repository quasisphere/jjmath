import JJMath.Hyperbolic.Converse.Continuation.CanonicalLoopPSL

/-!
# Split analytic continuation targets for the partial converse
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

namespace PathAnalyticContinuationData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- Representative-path values descend to path-homotopy classes. -/
def valueAt (C : PathAnalyticContinuationData x₀ g localModels)
    (x : X) : Path.Homotopic.Quotient x₀ x → ℍ :=
  Quotient.lift (fun p : Path x₀ x => C.valueAlong p) <| by
    intro p q hp
    exact C.value_homotopic hp

/-- Representative-path model centers descend to path-homotopy classes. -/
def centerAt (C : PathAnalyticContinuationData x₀ g localModels)
    (x : X) : Path.Homotopic.Quotient x₀ x → X :=
  Quotient.lift (fun p : Path x₀ x => C.centerAlong p) <| by
    intro p q hp
    exact C.center_homotopic hp

/-- Representative-path Mobius branches descend to path-homotopy classes. -/
def mobiusAt (C : PathAnalyticContinuationData x₀ g localModels)
    (x : X) :
    Path.Homotopic.Quotient x₀ x → RealMobiusRepresentative :=
  Quotient.lift (fun p : Path x₀ x => C.mobiusAlong p) <| by
    intro p q hp
    exact C.mobius_homotopic hp

/-- Representative-path sheet neighborhoods descend to path-homotopy classes. -/
def neighborhoodAt (C : PathAnalyticContinuationData x₀ g localModels)
    (x : X) :
    Path.Homotopic.Quotient x₀ x →
      Set (PathHomotopyUniversalCover X x₀) :=
  Quotient.lift (fun p : Path x₀ x => C.neighborhoodAlong p) <| by
    intro p q hp
    exact C.neighborhood_homotopic hp

end PathAnalyticContinuationData

/--
Terminal-branch data for analytic continuation along representative paths.

This is a stricter pre-quotient boundary than `PathAnalyticContinuationData`:
the value obtained after continuing along a path is forced to be the selected
terminal upper-half-plane model, postcomposed by the terminal real Mobius
representative.
-/
structure PathTerminalBranchAnalyticContinuationData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- The selected local model at the endpoint of the continued branch. -/
  centerAlong : ∀ {x : X}, Path x₀ x → X
  /-- The terminal real Mobius postcomposition for the continued branch. -/
  mobiusAlong : ∀ {x : X}, Path x₀ x → RealMobiusRepresentative
  /-- A sheet neighborhood on which the terminal branch formula is valid. -/
  neighborhoodAlong :
    ∀ {x : X}, Path x₀ x → Set (PathHomotopyUniversalCover X x₀)
  /-- The endpoint of the path lies in the terminal model domain. -/
  endpoint_mem_terminal_domain :
    ∀ {x : X} (p : Path x₀ x),
      x ∈ (localModels.chartAt (centerAlong p)).domain
  /-- The selected local model descends through endpoint-fixed path homotopy. -/
  center_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      centerAlong p = centerAlong q
  /-- The terminal real Mobius representative descends through path homotopy. -/
  mobius_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      mobiusAlong p = mobiusAlong q
  /-- The terminal sheet neighborhood descends through path homotopy. -/
  neighborhood_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      neighborhoodAlong p = neighborhoodAlong q
  /-- The terminal sheet is open. -/
  isOpen_neighborhoodAlong :
    ∀ {x : X} (p : Path x₀ x), IsOpen (neighborhoodAlong p)
  /-- The represented path-class point lies in its terminal sheet. -/
  mem_neighborhoodAlong :
    ∀ {x : X} (p : Path x₀ x),
      (⟨x, Path.Homotopic.Quotient.mk p⟩ :
        PathHomotopyUniversalCover X x₀) ∈ neighborhoodAlong p
  /-- Points in the terminal sheet project into the terminal model domain. -/
  endpoint_mem_model_domain :
    ∀ {x : X} (p : Path x₀ x) y', y' ∈ neighborhoodAlong p →
      PathHomotopyUniversalCover.endpoint y' ∈
        (localModels.chartAt (centerAlong p)).domain
  /--
  On the terminal sheet, the terminal branch computed from any representative
  of the upstairs point agrees with the sheet formula determined by `p`.
  -/
  terminalValue_eq_on_neighborhood :
    ∀ {x : X} (p : Path x₀ x) (y' : PathHomotopyUniversalCover X x₀)
      (p' : Path x₀ (PathHomotopyUniversalCover.endpoint y')),
      y' ∈ neighborhoodAlong p →
      Path.Homotopic.Quotient.mk p' =
        PathHomotopyUniversalCover.pathClass y' →
      realMobiusRepresentativeAction (mobiusAlong p')
          ((localModels.chartAt (centerAlong p')).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y')) =
        realMobiusRepresentativeAction (mobiusAlong p)
          ((localModels.chartAt (centerAlong p)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y'))

namespace PathTerminalBranchAnalyticContinuationData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- The terminal branch value forced by path-terminal-branch data. -/
def terminalValue
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) : ℍ :=
  realMobiusRepresentativeAction (C.mobiusAlong p)
    ((localModels.chartAt (C.centerAlong p)).toUpperHalfPlane x)

omit [RiemannSurface X] in
/--
The terminal value forced by terminal-branch continuation is invariant under
endpoint-fixed homotopy of representative paths.
-/
theorem terminalValue_homotopic
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} {p q : Path x₀ x} (hp : Path.Homotopic p q) :
    C.terminalValue p = C.terminalValue q := by
  change
    realMobiusRepresentativeAction (C.mobiusAlong p)
        ((localModels.chartAt (C.centerAlong p)).toUpperHalfPlane x) =
      realMobiusRepresentativeAction (C.mobiusAlong q)
        ((localModels.chartAt (C.centerAlong q)).toUpperHalfPlane x)
  rw [C.center_homotopic hp, C.mobius_homotopic hp]

/--
The terminal value descends to endpoint and path-homotopy class before passing
to the canonical cover.
-/
def terminalValueAt
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    (x : X) : Path.Homotopic.Quotient x₀ x → ℍ :=
  Quotient.lift (fun p : Path x₀ x => C.terminalValue p) <| by
    intro p q hp
    exact C.terminalValue_homotopic hp

/-- The terminal local-model center descends to endpoint and path-homotopy class. -/
def terminalCenterAt
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    (x : X) : Path.Homotopic.Quotient x₀ x → X :=
  Quotient.lift (fun p : Path x₀ x => C.centerAlong p) <| by
    intro p q hp
    exact C.center_homotopic hp

/-- The terminal Mobius representative descends to endpoint and path-homotopy
class. -/
def terminalMobiusAt
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    (x : X) :
    Path.Homotopic.Quotient x₀ x → RealMobiusRepresentative :=
  Quotient.lift (fun p : Path x₀ x => C.mobiusAlong p) <| by
    intro p q hp
    exact C.mobius_homotopic hp

/-- Terminal sheet neighborhoods descend to endpoint and path-homotopy class. -/
def terminalNeighborhoodAt
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    (x : X) :
    Path.Homotopic.Quotient x₀ x →
      Set (PathHomotopyUniversalCover X x₀) :=
  Quotient.lift (fun p : Path x₀ x => C.neighborhoodAlong p) <| by
    intro p q hp
    exact C.neighborhood_homotopic hp

omit [RiemannSurface X] in
@[simp]
theorem terminalValueAt_mk
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalValueAt x (Path.Homotopic.Quotient.mk p) =
      C.terminalValue p :=
  rfl

omit [RiemannSurface X] in
@[simp]
theorem terminalCenterAt_mk
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalCenterAt x (Path.Homotopic.Quotient.mk p) =
      C.centerAlong p :=
  rfl

omit [RiemannSurface X] in
@[simp]
theorem terminalMobiusAt_mk
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalMobiusAt x (Path.Homotopic.Quotient.mk p) =
      C.mobiusAlong p :=
  rfl

omit [RiemannSurface X] in
@[simp]
theorem terminalNeighborhoodAt_mk
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalNeighborhoodAt x (Path.Homotopic.Quotient.mk p) =
      C.neighborhoodAlong p :=
  rfl

/-- Terminal-branch continuation data give representative-path continuation data. -/
def toPathAnalyticContinuationData
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels) :
    PathAnalyticContinuationData x₀ g localModels where
  valueAlong := fun {_} p => C.terminalValue p
  centerAlong := fun {_} p => C.centerAlong p
  mobiusAlong := fun {_} p => C.mobiusAlong p
  neighborhoodAlong := fun {_} p => C.neighborhoodAlong p
  value_homotopic := by
    intro x p q hp
    simp [terminalValue, C.center_homotopic hp, C.mobius_homotopic hp]
  center_homotopic := by
    intro x p q hp
    exact C.center_homotopic hp
  mobius_homotopic := by
    intro x p q hp
    exact C.mobius_homotopic hp
  neighborhood_homotopic := by
    intro x p q hp
    exact C.neighborhood_homotopic hp
  isOpen_neighborhoodAlong := by
    intro x p
    exact C.isOpen_neighborhoodAlong p
  mem_neighborhoodAlong := by
    intro x p
    exact C.mem_neighborhoodAlong p
  endpoint_mem_model_domain := by
    intro x p y' hy'
    exact C.endpoint_mem_model_domain p y' hy'
  value_eq_on_neighborhood := by
    intro x p y' p' hy' hclass
    exact C.terminalValue_eq_on_neighborhood p y' p' hy' hclass

omit [RiemannSurface X] in
@[simp]
theorem toPathAnalyticContinuationData_valueAlong
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.toPathAnalyticContinuationData.valueAlong p = C.terminalValue p :=
  rfl

/-- The canonical-cover developing map forced by terminal-branch continuation. -/
def coverDev
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels) :
    (canonicalContinuationCover x₀).total → ℍ :=
  fun y =>
    C.terminalValueAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)

/-- The terminal local-model center on the canonical cover. -/
def coverCenter
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels) :
    (canonicalContinuationCover x₀).total → X :=
  fun y =>
    C.terminalCenterAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)

/-- The terminal Mobius representative on the canonical cover. -/
def coverMobius
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels) :
    (canonicalContinuationCover x₀).total → RealMobiusRepresentative :=
  fun y =>
    C.terminalMobiusAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)

/-- The terminal sheet neighborhood on the canonical cover. -/
def coverNeighborhood
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels) :
    (canonicalContinuationCover x₀).total →
      Set (canonicalContinuationCover x₀).total :=
  fun y =>
    C.terminalNeighborhoodAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)

@[simp]
theorem coverDev_mk
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.coverDev
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      C.terminalValue p :=
  rfl

@[simp]
theorem coverCenter_mk
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.coverCenter
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      C.centerAlong p :=
  rfl

@[simp]
theorem coverMobius_mk
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.coverMobius
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      C.mobiusAlong p :=
  rfl

@[simp]
theorem coverNeighborhood_mk
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.coverNeighborhood
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      C.neighborhoodAlong p :=
  rfl

/--
Terminal-branch continuation data give sheetwise continuation data directly on
the canonical cover.
-/
def toCanonicalCoverLocalContinuationData
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels) :
    CanonicalCoverLocalContinuationData x₀ g localModels where
  dev := C.coverDev
  centerAt := C.coverCenter
  mobiusAt := C.coverMobius
  neighborhoodAt := C.coverNeighborhood
  isOpen_neighborhoodAt := by
    intro y
    rcases y with ⟨x, q⟩
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        simpa [coverNeighborhood, terminalNeighborhoodAt,
          PathHomotopyUniversalCover.endpoint,
          PathHomotopyUniversalCover.pathClass] using
          C.isOpen_neighborhoodAlong p
  mem_neighborhoodAt := by
    intro y
    rcases y with ⟨x, q⟩
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        simpa [coverNeighborhood, terminalNeighborhoodAt,
          PathHomotopyUniversalCover.endpoint,
          PathHomotopyUniversalCover.pathClass] using
          C.mem_neighborhoodAlong p
  projection_mem_model_domain := by
    intro y y' hy'
    rcases y with ⟨x, q⟩
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        simpa [coverCenter, coverNeighborhood, terminalCenterAt,
          terminalNeighborhoodAt, canonicalContinuationCover,
          PathHomotopyUniversalCover.endpoint,
          PathHomotopyUniversalCover.pathClass] using
          C.endpoint_mem_model_domain p y' hy'
  dev_eq_on_neighborhood := by
    intro y y' hy'
    rcases y with ⟨x, q⟩
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        rcases y' with ⟨x', q'⟩
        induction q' using Path.Homotopic.Quotient.ind with
        | mk p' =>
            simpa [coverDev, coverCenter, coverMobius, coverNeighborhood,
              terminalValueAt, terminalValue, terminalCenterAt,
              terminalMobiusAt, terminalNeighborhoodAt,
              canonicalContinuationCover, PathHomotopyUniversalCover.endpoint,
              PathHomotopyUniversalCover.pathClass] using
              C.terminalValue_eq_on_neighborhood p
                (⟨x', Path.Homotopic.Quotient.mk p'⟩ :
                  PathHomotopyUniversalCover X x₀)
                p' hy' rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_dev
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels) :
    C.toCanonicalCoverLocalContinuationData.dev = C.coverDev :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_centerAt
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels) :
    C.toCanonicalCoverLocalContinuationData.centerAt = C.coverCenter :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_mobiusAt
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels) :
    C.toCanonicalCoverLocalContinuationData.mobiusAt = C.coverMobius :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_neighborhoodAt
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels) :
    C.toCanonicalCoverLocalContinuationData.neighborhoodAt = C.coverNeighborhood :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_dev_mk
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.toCanonicalCoverLocalContinuationData.dev
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      C.terminalValue p :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_centerAt_mk
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.toCanonicalCoverLocalContinuationData.centerAt
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      C.centerAlong p :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_mobiusAt_mk
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.toCanonicalCoverLocalContinuationData.mobiusAt
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      C.mobiusAlong p :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_neighborhoodAt_mk
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.toCanonicalCoverLocalContinuationData.neighborhoodAt
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      C.neighborhoodAlong p :=
  rfl

/-- The terminal-branch cover sheet attached to a point is open. -/
theorem isOpen_coverNeighborhood
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    (y : (canonicalContinuationCover x₀).total) :
    IsOpen (C.coverNeighborhood y) := by
  simpa [coverNeighborhood] using
    C.toCanonicalCoverLocalContinuationData.isOpen_neighborhoodAt y

/-- A cover point lies in the terminal-branch sheet it determines. -/
theorem mem_coverNeighborhood
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    (y : (canonicalContinuationCover x₀).total) :
    y ∈ C.coverNeighborhood y := by
  simpa [coverNeighborhood] using
    C.toCanonicalCoverLocalContinuationData.mem_neighborhoodAt y

/--
Every point of a terminal-branch sheet projects into the terminal local model
domain attached to the sheet.
-/
theorem endpoint_mem_coverCenter_domain
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    (y y' : (canonicalContinuationCover x₀).total)
    (hy' : y' ∈ C.coverNeighborhood y) :
    PathHomotopyUniversalCover.endpoint y' ∈
      (localModels.chartAt (C.coverCenter y)).domain := by
  simpa [coverCenter, coverNeighborhood] using
    C.toCanonicalCoverLocalContinuationData.projection_mem_model_domain y y' hy'

/--
On a terminal-branch sheet, the canonical-cover value is exactly the terminal
local model of that sheet, postcomposed by its terminal real Mobius
representative.
-/
theorem coverDev_eq_on_coverNeighborhood
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    (y y' : (canonicalContinuationCover x₀).total)
    (hy' : y' ∈ C.coverNeighborhood y) :
    C.coverDev y' =
      realMobiusRepresentativeAction (C.coverMobius y)
        ((localModels.chartAt (C.coverCenter y)).toUpperHalfPlane
          (PathHomotopyUniversalCover.endpoint y')) := by
  simpa [coverDev, coverCenter, coverMobius, coverNeighborhood] using
    C.toCanonicalCoverLocalContinuationData.dev_eq_on_neighborhood y y' hy'

end PathTerminalBranchAnalyticContinuationData

/--
A finite chain of overlapping local-model branches along a representative path.

This records the mathematical boundary that terminal branches should come from
stepwise analytic continuation through finitely many selected upper-half-plane
models.  The chain samples the path at ordered parameters, requires successive
model domains to overlap, and records that adjacent normalized branches agree
at the actual subdivision handoff point.
-/
structure PathLocalModelContinuationChain
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g)
    {x : X} (p : Path x₀ x) where
  /-- Number of continuation steps. -/
  length : ℕ
  /-- Ordered path parameters at the vertices of the chain. -/
  parameterAt : Fin (length + 1) → unitInterval
  /-- The chain begins at the initial parameter. -/
  parameterAt_zero : parameterAt 0 = 0
  /-- The chain ends at the terminal parameter. -/
  parameterAt_last : parameterAt (Fin.last length) = 1
  /-- The parameters are weakly increasing. -/
  parameterAt_mono :
    ∀ k : Fin length,
      (parameterAt k.castSucc : ℝ) ≤ (parameterAt k.succ : ℝ)
  /-- Consecutive subdivision parameters are genuinely distinct. -/
  parameterAt_strictMono :
    ∀ k : Fin length,
      (parameterAt k.castSucc : ℝ) < (parameterAt k.succ : ℝ)
  /-- The local-model center used at each chain vertex. -/
  centerAt : Fin (length + 1) → X
  /-- The real Mobius postcomposition for the branch at each chain vertex. -/
  mobiusAt : Fin (length + 1) → RealMobiusRepresentative
  /-- The chain starts with the selected local model at the basepoint. -/
  initial_center_eq : centerAt 0 = x₀
  /-- The initial branch has identity Mobius normalization. -/
  initial_mobius_eq : mobiusAt 0 = 1
  /-- The sampled path point lies in its selected model domain. -/
  sample_mem_model_domain :
    ∀ i,
      p (parameterAt i) ∈ (localModels.chartAt (centerAt i)).domain
  /--
  Each subinterval of the representative path is contained in the model domain
  attached to the initial vertex of that subinterval.
  -/
  path_segment_mem_model_domain :
    ∀ k : Fin length, ∀ t : unitInterval,
      (parameterAt k.castSucc : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ (parameterAt k.succ : ℝ) →
      p t ∈ (localModels.chartAt (centerAt k.castSucc)).domain
  /-- The endpoint lies in the terminal model domain. -/
  terminal_endpoint_mem_domain :
    x ∈ (localModels.chartAt (centerAt (Fin.last length))).domain
  /-- Adjacent model domains overlap. -/
  adjacent_overlap_nonempty :
    ∀ k : Fin length,
      Set.Nonempty
        ((localModels.chartAt (centerAt k.castSucc)).domain ∩
          (localModels.chartAt (centerAt k.succ)).domain)
  /--
  Adjacent normalized branches agree at the actual subdivision handoff point.
  The identity-principle input needed to construct such a chain may be proved
  on the connected overlap component containing this point; the finite-chain
  bookkeeping itself only uses this pointwise gluing equality.
  -/
  adjacent_branch_agrees_at_transition :
    ∀ k : Fin length,
      realMobiusRepresentativeAction (mobiusAt k.succ)
          ((localModels.chartAt (centerAt k.succ)).toUpperHalfPlane
            (p (parameterAt k.succ))) =
        realMobiusRepresentativeAction (mobiusAt k.castSucc)
          ((localModels.chartAt (centerAt k.castSucc)).toUpperHalfPlane
            (p (parameterAt k.succ)))

namespace PathLocalModelContinuationChain

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    {x : X} {p : Path x₀ x}

/-- The initial local-model center selected by a finite continuation chain. -/
def initialCenter
    (C : PathLocalModelContinuationChain x₀ g localModels p) : X :=
  C.centerAt 0

/-- The initial Mobius representative selected by a finite continuation chain. -/
def initialMobius
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    RealMobiusRepresentative :=
  C.mobiusAt 0

/-- The terminal local-model center selected by a finite continuation chain. -/
def terminalCenter
    (C : PathLocalModelContinuationChain x₀ g localModels p) : X :=
  C.centerAt (Fin.last C.length)

/-- The terminal Mobius representative selected by a finite continuation chain. -/
def terminalMobius
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    RealMobiusRepresentative :=
  C.mobiusAt (Fin.last C.length)

/-- The normalized branch value at a sampled path point of the chain. -/
def branchValueAt
    (C : PathLocalModelContinuationChain x₀ g localModels p)
    (i : Fin (C.length + 1)) : ℍ :=
  realMobiusRepresentativeAction (C.mobiusAt i)
    ((localModels.chartAt (C.centerAt i)).toUpperHalfPlane
      (p (C.parameterAt i)))

/-- The normalized branch value along a subinterval of the chain. -/
def segmentBranchValue
    (C : PathLocalModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) (t : unitInterval) : ℍ :=
  realMobiusRepresentativeAction (C.mobiusAt k.castSucc)
    ((localModels.chartAt (C.centerAt k.castSucc)).toUpperHalfPlane (p t))

/-- The terminal value forced by a finite continuation chain. -/
def terminalValue
    (C : PathLocalModelContinuationChain x₀ g localModels p) : ℍ :=
  realMobiusRepresentativeAction C.terminalMobius
    ((localModels.chartAt C.terminalCenter).toUpperHalfPlane x)

omit [RiemannSurface X] in
@[simp]
theorem terminalCenter_def
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    C.terminalCenter = C.centerAt (Fin.last C.length) :=
  rfl

omit [RiemannSurface X] in
@[simp]
theorem terminalMobius_def
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    C.terminalMobius = C.mobiusAt (Fin.last C.length) :=
  rfl

omit [RiemannSurface X] in
@[simp]
theorem initialCenter_eq_basepoint
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    C.initialCenter = x₀ := by
  simpa [initialCenter] using C.initial_center_eq

omit [RiemannSurface X] in
@[simp]
theorem initialMobius_eq_one
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    C.initialMobius = 1 := by
  simpa [initialMobius] using C.initial_mobius_eq

omit [RiemannSurface X] in
/--
A finite continuation chain has at least one subinterval: the first and last
subdivision parameters are forced to be `0` and `1`.
-/
theorem length_pos
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    0 < C.length := by
  rcases C with
    ⟨length, parameterAt, parameterAt_zero, parameterAt_last, _parameterAt_mono,
      _parameterAt_strictMono, _centerAt, _mobiusAt, _initial_center_eq,
      _initial_mobius_eq, _sample_mem_model_domain,
      _path_segment_mem_model_domain, _terminal_endpoint_mem_domain,
      _adjacent_overlap_nonempty, _adjacent_branch_agrees_at_transition⟩
  dsimp
  cases length with
  | zero =>
      have h01 : (0 : unitInterval) = 1 :=
        parameterAt_zero.symm.trans (by simpa using parameterAt_last)
      have hreal : (0 : ℝ) = 1 := by
        simpa using congrArg (fun t : unitInterval => (t : ℝ)) h01
      norm_num at hreal
  | succ n =>
      simp

omit [RiemannSurface X] in
/-- The number of subintervals in a finite continuation chain is nonzero. -/
theorem length_ne_zero
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    C.length ≠ 0 :=
  Nat.ne_of_gt C.length_pos

/-- The first subinterval of a finite continuation chain. -/
def firstSegmentIndex
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    Fin C.length :=
  ⟨0, C.length_pos⟩

/-- The last subinterval of a finite continuation chain. -/
def lastSegmentIndex
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    Fin C.length :=
  ⟨C.length - 1, Nat.pred_lt C.length_ne_zero⟩

omit [RiemannSurface X] in
@[simp]
theorem firstSegmentIndex_castSucc
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    C.firstSegmentIndex.castSucc = (0 : Fin (C.length + 1)) := by
  ext
  simp [firstSegmentIndex]

omit [RiemannSurface X] in
@[simp]
theorem lastSegmentIndex_succ_eq_last
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    C.lastSegmentIndex.succ = Fin.last C.length := by
  ext
  change C.length - 1 + 1 = C.length
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt C.length_pos)

omit [RiemannSurface X] in
/-- Consecutive subdivision parameters are strictly ordered. -/
theorem parameterAt_castSucc_lt_succ
    (C : PathLocalModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    (C.parameterAt k.castSucc : ℝ) < (C.parameterAt k.succ : ℝ) :=
  C.parameterAt_strictMono k

omit [RiemannSurface X] in
/-- The weak monotonicity condition follows from the strict subdivision order. -/
theorem parameterAt_castSucc_le_succ_of_strict
    (C : PathLocalModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    (C.parameterAt k.castSucc : ℝ) ≤ (C.parameterAt k.succ : ℝ) :=
  le_of_lt (C.parameterAt_castSucc_lt_succ k)

omit [RiemannSurface X] in
/-- Consecutive subdivision vertices are distinct as unit-interval points. -/
theorem parameterAt_castSucc_ne_succ
    (C : PathLocalModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    C.parameterAt k.castSucc ≠ C.parameterAt k.succ := by
  intro h
  have hreal :
      (C.parameterAt k.castSucc : ℝ) = (C.parameterAt k.succ : ℝ) := by
    simp [h]
  exact (ne_of_lt (C.parameterAt_castSucc_lt_succ k)) hreal

omit [RiemannSurface X] in
/-- The basepoint lies in the initial model domain forced by the chain. -/
theorem basepoint_mem_initial_model_domain
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    x₀ ∈ (localModels.chartAt x₀).domain := by
  have hsample := C.sample_mem_model_domain 0
  simpa [C.parameterAt_zero, C.initial_center_eq] using hsample

omit [RiemannSurface X] in
/-- The initial branch value is the basepoint local model value. -/
theorem initialBranchValue_eq_baseModel
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    realMobiusRepresentativeAction (C.mobiusAt 0)
        ((localModels.chartAt (C.centerAt 0)).toUpperHalfPlane x₀) =
      (localModels.chartAt x₀).toUpperHalfPlane x₀ := by
  simp [C.initial_center_eq, C.initial_mobius_eq, realMobiusRepresentativeAction_one]

omit [RiemannSurface X] in
/-- The first sampled branch value is the basepoint local model value. -/
theorem branchValueAt_zero_eq_baseModel
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    C.branchValueAt 0 = (localModels.chartAt x₀).toUpperHalfPlane x₀ := by
  simpa [branchValueAt, C.parameterAt_zero] using
    C.initialBranchValue_eq_baseModel

omit [RiemannSurface X] in
/--
The segment branch is defined on the whole corresponding closed subinterval of
the representative path.
-/
theorem segmentBranchValue_mem_model_domain
    (C : PathLocalModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) {t : unitInterval}
    (ht_left : (C.parameterAt k.castSucc : ℝ) ≤ (t : ℝ))
    (ht_right : (t : ℝ) ≤ (C.parameterAt k.succ : ℝ)) :
    p t ∈ (localModels.chartAt (C.centerAt k.castSucc)).domain :=
  C.path_segment_mem_model_domain k t ht_left ht_right

omit [RiemannSurface X] in
/-- At the left endpoint, a segment branch gives the sampled branch value. -/
theorem segmentBranchValue_leftEndpoint
    (C : PathLocalModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    C.segmentBranchValue k (C.parameterAt k.castSucc) =
      C.branchValueAt k.castSucc :=
  rfl

omit [RiemannSurface X] in
/-- The first segment starts with the basepoint local model value. -/
theorem firstSegmentBranchValue_leftEndpoint_eq_baseModel
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    C.segmentBranchValue C.firstSegmentIndex
        (C.parameterAt C.firstSegmentIndex.castSucc) =
      (localModels.chartAt x₀).toUpperHalfPlane x₀ := by
  simpa [segmentBranchValue, branchValueAt] using
    C.branchValueAt_zero_eq_baseModel

omit [RiemannSurface X] in
/-- The endpoint lies in the domain of the terminal center of the chain. -/
theorem endpoint_mem_terminalCenter_domain
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    x ∈ (localModels.chartAt C.terminalCenter).domain := by
  simpa [terminalCenter] using C.terminal_endpoint_mem_domain

omit [RiemannSurface X] in
/--
The transition point between two consecutive subintervals lies in both
adjacent model domains.  Thus the nonempty overlap is forced by path coverage,
not merely postulated separately.
-/
theorem transitionPoint_mem_adjacent_overlap
    (C : PathLocalModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    p (C.parameterAt k.succ) ∈
      (localModels.chartAt (C.centerAt k.castSucc)).domain ∩
        (localModels.chartAt (C.centerAt k.succ)).domain := by
  constructor
  · exact C.path_segment_mem_model_domain k (C.parameterAt k.succ)
      (C.parameterAt_mono k) le_rfl
  · exact C.sample_mem_model_domain k.succ

omit [RiemannSurface X] in
/-- Adjacent overlap nonemptiness follows from the shared transition point. -/
theorem adjacent_overlap_nonempty_from_transition
    (C : PathLocalModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    Set.Nonempty
      ((localModels.chartAt (C.centerAt k.castSucc)).domain ∩
        (localModels.chartAt (C.centerAt k.succ)).domain) :=
  ⟨p (C.parameterAt k.succ), C.transitionPoint_mem_adjacent_overlap k⟩

omit [RiemannSurface X] in
/-- Adjacent normalized branches agree at the actual subdivision transition. -/
theorem adjacent_branch_eq_at_transition
    (C : PathLocalModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    realMobiusRepresentativeAction (C.mobiusAt k.succ)
        ((localModels.chartAt (C.centerAt k.succ)).toUpperHalfPlane
          (p (C.parameterAt k.succ))) =
      realMobiusRepresentativeAction (C.mobiusAt k.castSucc)
        ((localModels.chartAt (C.centerAt k.castSucc)).toUpperHalfPlane
          (p (C.parameterAt k.succ))) := by
  exact C.adjacent_branch_agrees_at_transition k

omit [RiemannSurface X] in
/--
The sampled value at the next vertex equals the previous branch evaluated at
the transition point.  This is the finite-chain form of analytic continuation
across one overlap.
-/
theorem branchValueAt_succ_eq_leftTransitionValue
    (C : PathLocalModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    C.branchValueAt k.succ =
      realMobiusRepresentativeAction (C.mobiusAt k.castSucc)
        ((localModels.chartAt (C.centerAt k.castSucc)).toUpperHalfPlane
          (p (C.parameterAt k.succ))) := by
  simpa [branchValueAt] using C.adjacent_branch_agrees_at_transition k

omit [RiemannSurface X] in
/--
At the right endpoint, a segment branch gives the next sampled value.  This is
the endpoint gluing statement for one finite continuation step.
-/
theorem segmentBranchValue_rightEndpoint
    (C : PathLocalModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) :
    C.segmentBranchValue k (C.parameterAt k.succ) =
      C.branchValueAt k.succ := by
  simpa [segmentBranchValue] using
    (C.branchValueAt_succ_eq_leftTransitionValue k).symm

omit [RiemannSurface X] in
/--
Adjacent segment branches glue at a shared subdivision vertex.  The hypothesis
`k.succ = l.castSucc` says that the right endpoint of segment `k` is the left
endpoint of segment `l`.
-/
theorem segmentBranchValue_glues_at_shared_endpoint
    (C : PathLocalModelContinuationChain x₀ g localModels p)
    (k l : Fin C.length) (h : k.succ = l.castSucc) :
    C.segmentBranchValue k (C.parameterAt k.succ) =
      C.segmentBranchValue l (C.parameterAt l.castSucc) := by
  rw [C.segmentBranchValue_rightEndpoint k,
    C.segmentBranchValue_leftEndpoint l, h]

omit [RiemannSurface X] in
/-- The terminal value of the chain is the last sampled branch value. -/
theorem terminalValue_eq_branchValueAt_last
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    C.terminalValue = C.branchValueAt (Fin.last C.length) := by
  simp [terminalValue, branchValueAt, terminalCenter, terminalMobius,
    C.parameterAt_last]

omit [RiemannSurface X] in
/--
If a subinterval ends at the final subdivision vertex, its segment branch value
at that endpoint is the terminal value of the whole chain.
-/
theorem segmentBranchValue_rightEndpoint_eq_terminalValue_of_succ_eq_last
    (C : PathLocalModelContinuationChain x₀ g localModels p)
    (k : Fin C.length) (hk : k.succ = Fin.last C.length) :
    C.segmentBranchValue k (C.parameterAt k.succ) = C.terminalValue := by
  rw [C.segmentBranchValue_rightEndpoint k, hk]
  exact C.terminalValue_eq_branchValueAt_last.symm

omit [RiemannSurface X] in
/-- The last segment ends at the terminal value of the whole chain. -/
theorem lastSegmentBranchValue_rightEndpoint_eq_terminalValue
    (C : PathLocalModelContinuationChain x₀ g localModels p) :
    C.segmentBranchValue C.lastSegmentIndex
        (C.parameterAt C.lastSegmentIndex.succ) =
      C.terminalValue :=
  C.segmentBranchValue_rightEndpoint_eq_terminalValue_of_succ_eq_last
    C.lastSegmentIndex C.lastSegmentIndex_succ_eq_last

end PathLocalModelContinuationChain

/--
Terminal-branch continuation data whose terminal branch is produced by a
finite chain of overlapping local models along each representative path.

The homotopy-invariance and sheet fields are stated for the terminal chain
output.  Thus this boundary separates the finite local analytic continuation
construction from the later quotienting and monodromy packaging.
-/
structure PathChainTerminalBranchAnalyticContinuationData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- A finite local-model continuation chain along each representative path. -/
  chainAlong :
    ∀ {x : X} (p : Path x₀ x),
      PathLocalModelContinuationChain x₀ g localModels p
  /-- A sheet neighborhood on which the terminal chain branch is valid. -/
  neighborhoodAlong :
    ∀ {x : X}, Path x₀ x → Set (PathHomotopyUniversalCover X x₀)
  /-- The terminal local model descends through endpoint-fixed path homotopy. -/
  terminalCenter_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      (chainAlong p).terminalCenter = (chainAlong q).terminalCenter
  /-- The terminal real Mobius representative descends through path homotopy. -/
  terminalMobius_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      (chainAlong p).terminalMobius = (chainAlong q).terminalMobius
  /-- The terminal sheet neighborhood descends through path homotopy. -/
  neighborhood_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      neighborhoodAlong p = neighborhoodAlong q
  /-- The terminal sheet is open. -/
  isOpen_neighborhoodAlong :
    ∀ {x : X} (p : Path x₀ x), IsOpen (neighborhoodAlong p)
  /-- The represented path-class point lies in its terminal sheet. -/
  mem_neighborhoodAlong :
    ∀ {x : X} (p : Path x₀ x),
      (⟨x, Path.Homotopic.Quotient.mk p⟩ :
        PathHomotopyUniversalCover X x₀) ∈ neighborhoodAlong p
  /-- Points in the terminal sheet project into the terminal chain model domain. -/
  endpoint_mem_model_domain :
    ∀ {x : X} (p : Path x₀ x) y', y' ∈ neighborhoodAlong p →
      PathHomotopyUniversalCover.endpoint y' ∈
        (localModels.chartAt ((chainAlong p).terminalCenter)).domain
  /--
  On the terminal sheet, the finite-chain terminal branch computed from any
  representative of the upstairs point agrees with the sheet formula
  determined by `p`.
  -/
  terminalValue_eq_on_neighborhood :
    ∀ {x : X} (p : Path x₀ x) (y' : PathHomotopyUniversalCover X x₀)
      (p' : Path x₀ (PathHomotopyUniversalCover.endpoint y')),
      y' ∈ neighborhoodAlong p →
      Path.Homotopic.Quotient.mk p' =
        PathHomotopyUniversalCover.pathClass y' →
      realMobiusRepresentativeAction ((chainAlong p').terminalMobius)
          ((localModels.chartAt ((chainAlong p').terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y')) =
        realMobiusRepresentativeAction ((chainAlong p).terminalMobius)
          ((localModels.chartAt ((chainAlong p).terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y'))

namespace PathChainTerminalBranchAnalyticContinuationData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- The terminal value forced by a finite-chain terminal branch. -/
def terminalValue
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) : ℍ :=
  realMobiusRepresentativeAction ((C.chainAlong p).terminalMobius)
    ((localModels.chartAt ((C.chainAlong p).terminalCenter)).toUpperHalfPlane x)

omit [RiemannSurface X] in
@[simp]
theorem terminalValue_eq_chain_terminalValue
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalValue p = (C.chainAlong p).terminalValue :=
  rfl

omit [RiemannSurface X] in
/--
The terminal value produced by finite-chain continuation is invariant under
endpoint-fixed homotopy of representative paths.
-/
theorem terminalValue_homotopic
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} {p q : Path x₀ x} (hp : Path.Homotopic p q) :
    C.terminalValue p = C.terminalValue q := by
  change
    realMobiusRepresentativeAction ((C.chainAlong p).terminalMobius)
        ((localModels.chartAt ((C.chainAlong p).terminalCenter)).toUpperHalfPlane x) =
      realMobiusRepresentativeAction ((C.chainAlong q).terminalMobius)
        ((localModels.chartAt ((C.chainAlong q).terminalCenter)).toUpperHalfPlane x)
  rw [C.terminalCenter_homotopic hp, C.terminalMobius_homotopic hp]

/--
The chain-terminal value descends to endpoint and path-homotopy class before
passing to the canonical cover.
-/
def terminalValueAt
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    (x : X) : Path.Homotopic.Quotient x₀ x → ℍ :=
  Quotient.lift (fun p : Path x₀ x => C.terminalValue p) <| by
    intro p q hp
    exact C.terminalValue_homotopic hp

/-- The terminal local-model center descends to endpoint and path-homotopy class. -/
def terminalCenterAt
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    (x : X) : Path.Homotopic.Quotient x₀ x → X :=
  Quotient.lift (fun p : Path x₀ x => (C.chainAlong p).terminalCenter) <| by
    intro p q hp
    exact C.terminalCenter_homotopic hp

/--
The terminal Mobius representative descends to endpoint and path-homotopy
class.
-/
def terminalMobiusAt
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    (x : X) :
    Path.Homotopic.Quotient x₀ x → RealMobiusRepresentative :=
  Quotient.lift (fun p : Path x₀ x => (C.chainAlong p).terminalMobius) <| by
    intro p q hp
    exact C.terminalMobius_homotopic hp

/-- Terminal sheet neighborhoods descend to endpoint and path-homotopy class. -/
def terminalNeighborhoodAt
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    (x : X) :
    Path.Homotopic.Quotient x₀ x →
      Set (PathHomotopyUniversalCover X x₀) :=
  Quotient.lift (fun p : Path x₀ x => C.neighborhoodAlong p) <| by
    intro p q hp
    exact C.neighborhood_homotopic hp

omit [RiemannSurface X] in
@[simp]
theorem terminalValueAt_mk
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalValueAt x (Path.Homotopic.Quotient.mk p) =
      C.terminalValue p :=
  rfl

omit [RiemannSurface X] in
@[simp]
theorem terminalCenterAt_mk
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalCenterAt x (Path.Homotopic.Quotient.mk p) =
      (C.chainAlong p).terminalCenter :=
  rfl

omit [RiemannSurface X] in
@[simp]
theorem terminalMobiusAt_mk
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalMobiusAt x (Path.Homotopic.Quotient.mk p) =
      (C.chainAlong p).terminalMobius :=
  rfl

omit [RiemannSurface X] in
@[simp]
theorem terminalNeighborhoodAt_mk
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalNeighborhoodAt x (Path.Homotopic.Quotient.mk p) =
      C.neighborhoodAlong p :=
  rfl

/--
Finite-chain terminal data give the previous terminal-branch boundary by
forgetting the intermediate overlaps while keeping the forced terminal formula.
-/
def toPathTerminalBranchAnalyticContinuationData
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels) :
    PathTerminalBranchAnalyticContinuationData x₀ g localModels where
  centerAlong := fun {_} p => (C.chainAlong p).terminalCenter
  mobiusAlong := fun {_} p => (C.chainAlong p).terminalMobius
  neighborhoodAlong := fun {_} p => C.neighborhoodAlong p
  endpoint_mem_terminal_domain := by
    intro x p
    exact (C.chainAlong p).endpoint_mem_terminalCenter_domain
  center_homotopic := by
    intro x p q hp
    exact C.terminalCenter_homotopic hp
  mobius_homotopic := by
    intro x p q hp
    exact C.terminalMobius_homotopic hp
  neighborhood_homotopic := by
    intro x p q hp
    exact C.neighborhood_homotopic hp
  isOpen_neighborhoodAlong := by
    intro x p
    exact C.isOpen_neighborhoodAlong p
  mem_neighborhoodAlong := by
    intro x p
    exact C.mem_neighborhoodAlong p
  endpoint_mem_model_domain := by
    intro x p y' hy'
    exact C.endpoint_mem_model_domain p y' hy'
  terminalValue_eq_on_neighborhood := by
    intro x p y' p' hy' hclass
    exact C.terminalValue_eq_on_neighborhood p y' p' hy' hclass

omit [RiemannSurface X] in
@[simp]
theorem toPathTerminalBranchAnalyticContinuationData_terminalValue
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.toPathTerminalBranchAnalyticContinuationData.terminalValue p =
      C.terminalValue p :=
  rfl

end PathChainTerminalBranchAnalyticContinuationData

/--
Finite-chain terminal continuation data with only value-level homotopy
descent.

This is the mathematically weaker quotient boundary beneath
`PathChainTerminalBranchAnalyticContinuationData`: homotopic representative
paths must give the same continued value, but the auxiliary terminal chart,
Mobius representative, and sheet neighborhood are allowed to be chosen from a
representative of each path class rather than literally equal for all
homotopic paths.
-/
structure PathChainTerminalBranchAnalyticContinuationValueData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- A finite local-model continuation chain along each representative path. -/
  chainAlong :
    ∀ {x : X} (p : Path x₀ x),
      PathLocalModelContinuationChain x₀ g localModels p
  /-- A sheet neighborhood on which the terminal chain branch is valid. -/
  neighborhoodAlong :
    ∀ {x : X}, Path x₀ x → Set (PathHomotopyUniversalCover X x₀)
  /-- The terminal value descends through endpoint-fixed path homotopy. -/
  terminalValue_homotopic :
    ∀ {x : X} {p q : Path x₀ x}, Path.Homotopic p q →
      (chainAlong p).terminalValue = (chainAlong q).terminalValue
  /-- The terminal sheet is open. -/
  isOpen_neighborhoodAlong :
    ∀ {x : X} (p : Path x₀ x), IsOpen (neighborhoodAlong p)
  /-- The represented path-class point lies in its terminal sheet. -/
  mem_neighborhoodAlong :
    ∀ {x : X} (p : Path x₀ x),
      (⟨x, Path.Homotopic.Quotient.mk p⟩ :
        PathHomotopyUniversalCover X x₀) ∈ neighborhoodAlong p
  /-- Points in the terminal sheet project into the terminal chain model domain. -/
  endpoint_mem_model_domain :
    ∀ {x : X} (p : Path x₀ x) y', y' ∈ neighborhoodAlong p →
      PathHomotopyUniversalCover.endpoint y' ∈
        (localModels.chartAt ((chainAlong p).terminalCenter)).domain
  /--
  On the terminal sheet, the finite-chain terminal branch computed from any
  representative of the upstairs point agrees with the sheet formula
  determined by `p`.
  -/
  terminalValue_eq_on_neighborhood :
    ∀ {x : X} (p : Path x₀ x) (y' : PathHomotopyUniversalCover X x₀)
      (p' : Path x₀ (PathHomotopyUniversalCover.endpoint y')),
      y' ∈ neighborhoodAlong p →
      Path.Homotopic.Quotient.mk p' =
        PathHomotopyUniversalCover.pathClass y' →
      realMobiusRepresentativeAction ((chainAlong p').terminalMobius)
          ((localModels.chartAt ((chainAlong p').terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y')) =
        realMobiusRepresentativeAction ((chainAlong p).terminalMobius)
          ((localModels.chartAt ((chainAlong p).terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y'))

namespace PathChainTerminalBranchAnalyticContinuationValueData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- The terminal value forced by a finite-chain terminal branch. -/
def terminalValue
    (C : PathChainTerminalBranchAnalyticContinuationValueData x₀ g localModels)
    {x : X} (p : Path x₀ x) : ℍ :=
  (C.chainAlong p).terminalValue

omit [RiemannSurface X] in
@[simp]
theorem terminalValue_eq_chain_terminalValue
    (C : PathChainTerminalBranchAnalyticContinuationValueData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalValue p = (C.chainAlong p).terminalValue :=
  rfl

omit [ChartedSpace ℂ X] [RiemannSurface X] in
theorem out_homotopic_mk
    {x : X} (p : Path x₀ x) :
    Path.Homotopic
      (Quot.out (Path.Homotopic.Quotient.mk p))
      p := by
  exact
    (Path.Homotopic.Quotient.eq).mp
      (Quot.out_eq (Path.Homotopic.Quotient.mk p))

end PathChainTerminalBranchAnalyticContinuationValueData

/--
Analytic continuation indexed by endpoint and path-homotopy class.

This is the path-homotopy-cover boundary before packaging the data as a
cover-level map.  A value at a point of the canonical cover is obtained from
the endpoint together with the stored homotopy class of paths from the
basepoint.  The sheet fields say that these path-class values locally agree
with one of the selected upper-half-plane models up to a real Mobius
postcomposition.
-/
structure PathClassAnalyticContinuationData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
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

namespace PathClassAnalyticContinuationData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- The cover-level developing map determined by path-class continuation data. -/
def dev (C : PathClassAnalyticContinuationData x₀ g localModels) :
    (canonicalContinuationCover x₀).total → ℍ :=
  fun y =>
    C.valueAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)

/--
Path-class continuation data folds into the sheetwise continuation data on the
canonical cover.
-/
def toCanonicalCoverLocalContinuationData
    (C : PathClassAnalyticContinuationData x₀ g localModels) :
    CanonicalCoverLocalContinuationData x₀ g localModels where
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

@[simp]
theorem toCanonicalCoverLocalContinuationData_dev
    (C : PathClassAnalyticContinuationData x₀ g localModels) :
    C.toCanonicalCoverLocalContinuationData.dev = C.dev :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_centerAt
    (C : PathClassAnalyticContinuationData x₀ g localModels)
    (y : (canonicalContinuationCover x₀).total) :
    C.toCanonicalCoverLocalContinuationData.centerAt y =
      C.centerAt (PathHomotopyUniversalCover.endpoint y)
        (PathHomotopyUniversalCover.pathClass y) :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_mobiusAt
    (C : PathClassAnalyticContinuationData x₀ g localModels)
    (y : (canonicalContinuationCover x₀).total) :
    C.toCanonicalCoverLocalContinuationData.mobiusAt y =
      C.mobiusAt (PathHomotopyUniversalCover.endpoint y)
        (PathHomotopyUniversalCover.pathClass y) :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_neighborhoodAt
    (C : PathClassAnalyticContinuationData x₀ g localModels)
    (y : (canonicalContinuationCover x₀).total) :
    C.toCanonicalCoverLocalContinuationData.neighborhoodAt y =
      C.neighborhoodAt (PathHomotopyUniversalCover.endpoint y)
        (PathHomotopyUniversalCover.pathClass y) :=
  rfl

end PathClassAnalyticContinuationData

namespace PathChainTerminalBranchAnalyticContinuationValueData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/--
The terminal value at a path-homotopy class, computed from Lean's chosen
representative and justified by value-level homotopy descent.
-/
noncomputable def terminalValueAt
    (C : PathChainTerminalBranchAnalyticContinuationValueData x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) : ℍ :=
  C.terminalValue (Quot.out q)

/-- The terminal center attached to Lean's chosen representative of a path class. -/
noncomputable def terminalCenterAt
    (C : PathChainTerminalBranchAnalyticContinuationValueData x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) : X :=
  (C.chainAlong (Quot.out q)).terminalCenter

/-- The terminal Mobius representative attached to Lean's chosen representative. -/
noncomputable def terminalMobiusAt
    (C : PathChainTerminalBranchAnalyticContinuationValueData x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) :
    RealMobiusRepresentative :=
  (C.chainAlong (Quot.out q)).terminalMobius

/-- The terminal sheet attached to Lean's chosen representative of a path class. -/
noncomputable def terminalNeighborhoodAt
    (C : PathChainTerminalBranchAnalyticContinuationValueData x₀ g localModels)
    (x : X) (q : Path.Homotopic.Quotient x₀ x) :
    Set (PathHomotopyUniversalCover X x₀) :=
  C.neighborhoodAlong (Quot.out q)

omit [RiemannSurface X] in
@[simp]
theorem terminalValueAt_mk
    (C : PathChainTerminalBranchAnalyticContinuationValueData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.terminalValueAt x (Path.Homotopic.Quotient.mk p) =
      C.terminalValue p := by
  exact C.terminalValue_homotopic (out_homotopic_mk p)

/--
Value-level finite-chain continuation data descend to path-class continuation
data.  Unlike the stronger terminal-branch package, this quotient step does
not require the auxiliary terminal chart, Mobius representative, or sheet
neighborhood to be homotopy invariant as literal choices.
-/
noncomputable def toPathClassAnalyticContinuationData
    (C : PathChainTerminalBranchAnalyticContinuationValueData x₀ g localModels) :
    PathClassAnalyticContinuationData x₀ g localModels where
  valueAt := C.terminalValueAt
  centerAt := C.terminalCenterAt
  mobiusAt := C.terminalMobiusAt
  neighborhoodAt := C.terminalNeighborhoodAt
  isOpen_neighborhoodAt := by
    intro x q
    exact C.isOpen_neighborhoodAlong (Quot.out q)
  mem_neighborhoodAt := by
    intro x q
    have hmem := C.mem_neighborhoodAlong (Quot.out q)
    have hpoint :
        (⟨x, q⟩ : PathHomotopyUniversalCover X x₀) =
          ⟨x, Path.Homotopic.Quotient.mk (Quot.out q)⟩ := by
      exact Sigma.ext rfl (heq_of_eq (Quot.out_eq q).symm)
    simpa [terminalNeighborhoodAt, hpoint] using hmem
  endpoint_mem_model_domain := by
    intro x q y' hy'
    exact C.endpoint_mem_model_domain (Quot.out q) y' hy'
  value_eq_on_neighborhood := by
    intro x q y' hy'
    let p : Path x₀ x := Quot.out q
    let p' : Path x₀ (PathHomotopyUniversalCover.endpoint y') :=
      Quot.out (PathHomotopyUniversalCover.pathClass y')
    have hclass :
        Path.Homotopic.Quotient.mk p' =
          PathHomotopyUniversalCover.pathClass y' := by
      exact Quot.out_eq (PathHomotopyUniversalCover.pathClass y')
    simpa [terminalValueAt, terminalValue, terminalCenterAt,
      terminalMobiusAt, terminalNeighborhoodAt, p, p'] using
      C.terminalValue_eq_on_neighborhood p y' p' hy' hclass

/--
Value-level finite-chain continuation data give sheetwise continuation data
directly on the canonical cover.
-/
noncomputable def toCanonicalCoverLocalContinuationData
    (C : PathChainTerminalBranchAnalyticContinuationValueData x₀ g localModels) :
    CanonicalCoverLocalContinuationData x₀ g localModels :=
  C.toPathClassAnalyticContinuationData.toCanonicalCoverLocalContinuationData

end PathChainTerminalBranchAnalyticContinuationValueData

namespace PathChainTerminalBranchAnalyticContinuationData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/--
Forget literal homotopy invariance of auxiliary terminal chart data, retaining
only the value-level descent needed for quotienting.
-/
def toPathChainTerminalBranchAnalyticContinuationValueData
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels) :
    PathChainTerminalBranchAnalyticContinuationValueData x₀ g localModels where
  chainAlong := C.chainAlong
  neighborhoodAlong := C.neighborhoodAlong
  terminalValue_homotopic := by
    intro x p q hp
    exact C.terminalValue_homotopic hp
  isOpen_neighborhoodAlong := C.isOpen_neighborhoodAlong
  mem_neighborhoodAlong := C.mem_neighborhoodAlong
  endpoint_mem_model_domain := C.endpoint_mem_model_domain
  terminalValue_eq_on_neighborhood := C.terminalValue_eq_on_neighborhood

end PathChainTerminalBranchAnalyticContinuationData

namespace PathTerminalBranchAnalyticContinuationData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/--
Terminal-branch continuation data descend directly to path-class continuation
data, preserving that values are terminal local-model values rather than
independent path values.
-/
def toPathClassAnalyticContinuationData
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels) :
    PathClassAnalyticContinuationData x₀ g localModels where
  valueAt := C.terminalValueAt
  centerAt := C.terminalCenterAt
  mobiusAt := C.terminalMobiusAt
  neighborhoodAt := C.terminalNeighborhoodAt
  isOpen_neighborhoodAt := by
    intro x q
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        simpa [terminalNeighborhoodAt] using C.isOpen_neighborhoodAlong p
  mem_neighborhoodAt := by
    intro x q
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        simpa [terminalNeighborhoodAt] using C.mem_neighborhoodAlong p
  endpoint_mem_model_domain := by
    intro x q y' hy'
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        simpa [terminalCenterAt, terminalNeighborhoodAt] using
          C.endpoint_mem_model_domain p y' hy'
  value_eq_on_neighborhood := by
    intro x q y' hy'
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        rcases y' with ⟨x', q'⟩
        induction q' using Path.Homotopic.Quotient.ind with
        | mk p' =>
            simpa [terminalValueAt, terminalValue, terminalCenterAt,
              terminalMobiusAt, terminalNeighborhoodAt,
              PathHomotopyUniversalCover.endpoint,
              PathHomotopyUniversalCover.pathClass] using
              C.terminalValue_eq_on_neighborhood p
                (⟨x', Path.Homotopic.Quotient.mk p'⟩ :
                  PathHomotopyUniversalCover X x₀)
                p' hy' rfl

omit [RiemannSurface X] in
@[simp]
theorem toPathClassAnalyticContinuationData_valueAt_mk
    (C : PathTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.toPathClassAnalyticContinuationData.valueAt x
        (Path.Homotopic.Quotient.mk p) =
      C.terminalValue p :=
  rfl

end PathTerminalBranchAnalyticContinuationData

namespace PathChainTerminalBranchAnalyticContinuationData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- The canonical-cover developing map forced by finite-chain continuation. -/
def coverDev
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels) :
    (canonicalContinuationCover x₀).total → ℍ :=
  fun y =>
    C.terminalValueAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)

/-- The terminal local-model center on the canonical cover. -/
def coverCenter
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels) :
    (canonicalContinuationCover x₀).total → X :=
  fun y =>
    C.terminalCenterAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)

/-- The terminal Mobius representative on the canonical cover. -/
def coverMobius
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels) :
    (canonicalContinuationCover x₀).total → RealMobiusRepresentative :=
  fun y =>
    C.terminalMobiusAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)

/-- The terminal sheet neighborhood on the canonical cover. -/
def coverNeighborhood
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels) :
    (canonicalContinuationCover x₀).total →
      Set (canonicalContinuationCover x₀).total :=
  fun y =>
    C.terminalNeighborhoodAt (PathHomotopyUniversalCover.endpoint y)
      (PathHomotopyUniversalCover.pathClass y)

@[simp]
theorem coverDev_mk
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.coverDev
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      C.terminalValue p :=
  rfl

@[simp]
theorem coverCenter_mk
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.coverCenter
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      (C.chainAlong p).terminalCenter :=
  rfl

@[simp]
theorem coverMobius_mk
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.coverMobius
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      (C.chainAlong p).terminalMobius :=
  rfl

@[simp]
theorem coverNeighborhood_mk
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.coverNeighborhood
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      C.neighborhoodAlong p :=
  rfl

/--
Finite-chain terminal continuation data descend directly to path-class
continuation data.  This keeps the finite-chain provenance visible at the
path-homotopy quotient stage, before any cover-level packaging.
-/
def toPathClassAnalyticContinuationData
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels) :
    PathClassAnalyticContinuationData x₀ g localModels where
  valueAt := C.terminalValueAt
  centerAt := C.terminalCenterAt
  mobiusAt := C.terminalMobiusAt
  neighborhoodAt := C.terminalNeighborhoodAt
  isOpen_neighborhoodAt := by
    intro x q
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        simpa [terminalNeighborhoodAt] using C.isOpen_neighborhoodAlong p
  mem_neighborhoodAt := by
    intro x q
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        simpa [terminalNeighborhoodAt] using C.mem_neighborhoodAlong p
  endpoint_mem_model_domain := by
    intro x q y' hy'
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        simpa [terminalCenterAt, terminalNeighborhoodAt] using
          C.endpoint_mem_model_domain p y' hy'
  value_eq_on_neighborhood := by
    intro x q y' hy'
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        rcases y' with ⟨x', q'⟩
        induction q' using Path.Homotopic.Quotient.ind with
        | mk p' =>
            simpa [terminalValueAt, terminalValue, terminalCenterAt,
              terminalMobiusAt, terminalNeighborhoodAt,
              PathHomotopyUniversalCover.endpoint,
              PathHomotopyUniversalCover.pathClass] using
              C.terminalValue_eq_on_neighborhood p
                (⟨x', Path.Homotopic.Quotient.mk p'⟩ :
                  PathHomotopyUniversalCover X x₀)
                p' hy' rfl

omit [RiemannSurface X] in
@[simp]
theorem toPathClassAnalyticContinuationData_valueAt_mk
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.toPathClassAnalyticContinuationData.valueAt x
        (Path.Homotopic.Quotient.mk p) =
      C.terminalValue p :=
  rfl

/--
Finite-chain terminal continuation data give sheetwise continuation data
directly on the canonical cover.
-/
def toCanonicalCoverLocalContinuationData
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels) :
    CanonicalCoverLocalContinuationData x₀ g localModels :=
  C.toPathClassAnalyticContinuationData.toCanonicalCoverLocalContinuationData

@[simp]
theorem toCanonicalCoverLocalContinuationData_dev
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels) :
    C.toCanonicalCoverLocalContinuationData.dev = C.coverDev :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_centerAt
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels) :
    C.toCanonicalCoverLocalContinuationData.centerAt = C.coverCenter :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_mobiusAt
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels) :
    C.toCanonicalCoverLocalContinuationData.mobiusAt = C.coverMobius :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_neighborhoodAt
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels) :
    C.toCanonicalCoverLocalContinuationData.neighborhoodAt = C.coverNeighborhood :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_dev_mk
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.toCanonicalCoverLocalContinuationData.dev
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      C.terminalValue p :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_centerAt_mk
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.toCanonicalCoverLocalContinuationData.centerAt
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      (C.chainAlong p).terminalCenter :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_mobiusAt_mk
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.toCanonicalCoverLocalContinuationData.mobiusAt
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      (C.chainAlong p).terminalMobius :=
  rfl

@[simp]
theorem toCanonicalCoverLocalContinuationData_neighborhoodAt_mk
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.toCanonicalCoverLocalContinuationData.neighborhoodAt
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      C.neighborhoodAlong p :=
  rfl

/-- The finite-chain cover sheet attached to a point is open. -/
theorem isOpen_coverNeighborhood
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    (y : (canonicalContinuationCover x₀).total) :
    IsOpen (C.coverNeighborhood y) := by
  simpa [coverNeighborhood] using
    C.toCanonicalCoverLocalContinuationData.isOpen_neighborhoodAt y

/-- A cover point lies in the finite-chain terminal sheet it determines. -/
theorem mem_coverNeighborhood
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    (y : (canonicalContinuationCover x₀).total) :
    y ∈ C.coverNeighborhood y := by
  simpa [coverNeighborhood] using
    C.toCanonicalCoverLocalContinuationData.mem_neighborhoodAt y

/--
Every point of a finite-chain terminal sheet projects into the terminal local
model domain attached to the sheet.
-/
theorem endpoint_mem_coverCenter_domain
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    (y y' : (canonicalContinuationCover x₀).total)
    (hy' : y' ∈ C.coverNeighborhood y) :
    PathHomotopyUniversalCover.endpoint y' ∈
      (localModels.chartAt (C.coverCenter y)).domain := by
  simpa [coverCenter, coverNeighborhood] using
    C.toCanonicalCoverLocalContinuationData.projection_mem_model_domain y y' hy'

/--
On a finite-chain terminal sheet, the canonical-cover value is exactly the
terminal local model of that sheet, postcomposed by its terminal real Mobius
representative.
-/
theorem coverDev_eq_on_coverNeighborhood
    (C : PathChainTerminalBranchAnalyticContinuationData x₀ g localModels)
    (y y' : (canonicalContinuationCover x₀).total)
    (hy' : y' ∈ C.coverNeighborhood y) :
    C.coverDev y' =
      realMobiusRepresentativeAction (C.coverMobius y)
        ((localModels.chartAt (C.coverCenter y)).toUpperHalfPlane
          (PathHomotopyUniversalCover.endpoint y')) := by
  simpa [coverDev, coverCenter, coverMobius, coverNeighborhood] using
    C.toCanonicalCoverLocalContinuationData.dev_eq_on_neighborhood y y' hy'

end PathChainTerminalBranchAnalyticContinuationData

namespace PathAnalyticContinuationData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- Actual-path continuation data descend to path-class continuation data. -/
def toPathClassAnalyticContinuationData
    (C : PathAnalyticContinuationData x₀ g localModels) :
    PathClassAnalyticContinuationData x₀ g localModels where
  valueAt := C.valueAt
  centerAt := C.centerAt
  mobiusAt := C.mobiusAt
  neighborhoodAt := C.neighborhoodAt
  isOpen_neighborhoodAt := by
    intro x q
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        simpa [neighborhoodAt] using C.isOpen_neighborhoodAlong p
  mem_neighborhoodAt := by
    intro x q
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        simpa [neighborhoodAt] using C.mem_neighborhoodAlong p
  endpoint_mem_model_domain := by
    intro x q y' hy'
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        simpa [centerAt, neighborhoodAt] using
          C.endpoint_mem_model_domain p y' hy'
  value_eq_on_neighborhood := by
    intro x q y' hy'
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        rcases y' with ⟨x', q'⟩
        induction q' using Path.Homotopic.Quotient.ind with
        | mk p' =>
            simpa [valueAt, centerAt, mobiusAt, neighborhoodAt,
              PathHomotopyUniversalCover.endpoint,
              PathHomotopyUniversalCover.pathClass] using
              C.value_eq_on_neighborhood p
                (⟨x', Path.Homotopic.Quotient.mk p'⟩ :
                  PathHomotopyUniversalCover X x₀)
                p' hy' rfl

omit [RiemannSurface X] in
@[simp]
theorem toPathClassAnalyticContinuationData_valueAt_mk
    (C : PathAnalyticContinuationData x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    C.toPathClassAnalyticContinuationData.valueAt x
        (Path.Homotopic.Quotient.mk p) =
      C.valueAlong p :=
  rfl

end PathAnalyticContinuationData

/--
Monodromy data for analytic continuation along actual representative paths.

The equivariance field is the pre-quotient monodromy statement: continuing
after first traversing the inverse loop representing `γ` changes the value by
the lifted real Mobius holonomy.
-/
structure PathAnalyticContinuationMonodromyData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- Continuation data indexed by representative paths. -/
  pathContinuation : PathAnalyticContinuationData x₀ g localModels
  /-- Lifted real holonomy obtained from loop monodromy. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Loop-precomposition of representative paths gives the lifted Mobius action. -/
  path_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x),
      Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
      pathContinuation.valueAlong (loop.trans p) =
        holonomyLift.upperHalfPlaneAction γ
          (pathContinuation.valueAlong p)

namespace PathAnalyticContinuationMonodromyData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

end PathAnalyticContinuationMonodromyData

/--
Loop-equivariance data for already constructed representative-path
continuation.

This separates construction and endpoint-fixed homotopy descent of continued
branches from the monodromy assertion for loop precomposition.
-/
structure PathAnalyticContinuationEquivarianceData
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (pathContinuation :
      PathAnalyticContinuationData x₀ g localModels) where
  /-- Lifted real holonomy obtained from loop monodromy. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Loop-precomposition of representative paths gives the lifted Mobius action. -/
  path_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x),
      Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
      pathContinuation.valueAlong (loop.trans p) =
        holonomyLift.upperHalfPlaneAction γ
          (pathContinuation.valueAlong p)

namespace PathAnalyticContinuationEquivarianceData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    {C : PathAnalyticContinuationData x₀ g localModels}

/--
Representative-path continuation data together with loop equivariance give the
representative-path monodromy package.
-/
def toPathAnalyticContinuationMonodromyData
    (E : PathAnalyticContinuationEquivarianceData C) :
    PathAnalyticContinuationMonodromyData x₀ g localModels where
  pathContinuation := C
  holonomyLift := E.holonomyLift
  path_equivariant := E.path_equivariant

end PathAnalyticContinuationEquivarianceData

/--
Monodromy data for terminal-branch analytic continuation along representative
paths.

The continued value is not stored independently: it is the terminal branch
value forced by `PathTerminalBranchAnalyticContinuationData`.
-/
structure PathTerminalBranchAnalyticContinuationMonodromyData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- Terminal branch data indexed by representative paths. -/
  terminalContinuation :
    PathTerminalBranchAnalyticContinuationData x₀ g localModels
  /-- Lifted real holonomy obtained from loop monodromy. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Loop-precomposition of paths gives the lifted Mobius action on terminal values. -/
  terminal_path_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x),
      Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
      terminalContinuation.terminalValue (loop.trans p) =
        holonomyLift.upperHalfPlaneAction γ
          (terminalContinuation.terminalValue p)

namespace PathTerminalBranchAnalyticContinuationMonodromyData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- Terminal-branch monodromy data give representative-path monodromy data. -/
def toPathAnalyticContinuationMonodromyData
    (M :
      PathTerminalBranchAnalyticContinuationMonodromyData
        x₀ g localModels) :
    PathAnalyticContinuationMonodromyData x₀ g localModels where
  pathContinuation := M.terminalContinuation.toPathAnalyticContinuationData
  holonomyLift := M.holonomyLift
  path_equivariant := by
    intro γ loop x p hloop
    simpa [PathTerminalBranchAnalyticContinuationData.toPathAnalyticContinuationData] using
      M.terminal_path_equivariant γ loop p hloop

end PathTerminalBranchAnalyticContinuationMonodromyData

/--
Monodromy data for finite-chain terminal-branch analytic continuation.

This is the sharpest currently exposed boundary: terminal values are forced by
finite overlap chains, and loop-precomposition changes those values by the
lifted real Mobius holonomy.
-/
structure PathChainTerminalBranchAnalyticContinuationMonodromyData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- Finite-chain terminal continuation data indexed by representative paths. -/
  chainTerminalContinuation :
    PathChainTerminalBranchAnalyticContinuationData x₀ g localModels
  /-- Lifted real holonomy obtained from loop monodromy. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Loop-precomposition of paths gives the lifted Mobius action on chain values. -/
  chain_terminal_path_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x),
      Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
      chainTerminalContinuation.terminalValue (loop.trans p) =
        holonomyLift.upperHalfPlaneAction γ
          (chainTerminalContinuation.terminalValue p)

namespace PathChainTerminalBranchAnalyticContinuationMonodromyData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/--
Finite-chain terminal monodromy data give terminal-branch monodromy data by
forgetting the intermediate chain vertices.
-/
def toPathTerminalBranchAnalyticContinuationMonodromyData
    (M :
      PathChainTerminalBranchAnalyticContinuationMonodromyData
        x₀ g localModels) :
    PathTerminalBranchAnalyticContinuationMonodromyData x₀ g localModels where
  terminalContinuation :=
    M.chainTerminalContinuation.toPathTerminalBranchAnalyticContinuationData
  holonomyLift := M.holonomyLift
  terminal_path_equivariant := by
    intro γ loop x p hloop
    simpa using M.chain_terminal_path_equivariant γ loop p hloop

end PathChainTerminalBranchAnalyticContinuationMonodromyData

/--
Path-class monodromy data.

The equivariance field is written before any cover-level map is introduced: it
says that left-composing the stored path class by the inverse of a loop acts on
continued values through the corresponding lifted real Mobius holonomy.
-/
structure PathClassAnalyticContinuationMonodromyData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- Continuation data indexed by path-homotopy classes. -/
  pathClassContinuation :
    PathClassAnalyticContinuationData x₀ g localModels
  /-- Lifted real holonomy obtained from monodromy around loops. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Loop action on path classes matches the lifted real Mobius action on values. -/
  pathClass_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (x : X)
      (q : Path.Homotopic.Quotient x₀ x),
      pathClassContinuation.valueAt x
          (Path.Homotopic.Quotient.trans (FundamentalGroup.toPath γ⁻¹) q) =
        holonomyLift.upperHalfPlaneAction γ
          (pathClassContinuation.valueAt x q)

namespace PathClassAnalyticContinuationMonodromyData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- Path-class monodromy data give the cover-level monodromy boundary. -/
def toAnalyticContinuationMonodromyData
    (M : PathClassAnalyticContinuationMonodromyData x₀ g localModels) :
    AnalyticContinuationMonodromyData x₀ g localModels where
  localContinuation :=
    M.pathClassContinuation.toCanonicalCoverLocalContinuationData
  holonomyLift := M.holonomyLift
  equivariant := by
    intro γ y
    simpa [PathClassAnalyticContinuationData.dev, canonicalContinuationCover,
      SimplyConnectedCover.deckAction, PathHomotopyUniversalCover.deckHomeomorphism_apply,
      PathHomotopyUniversalCover.deckAction, PathHomotopyUniversalCover.endpoint,
      PathHomotopyUniversalCover.pathClass] using
      M.pathClass_equivariant γ (PathHomotopyUniversalCover.endpoint y)
        (PathHomotopyUniversalCover.pathClass y)

end PathClassAnalyticContinuationMonodromyData

/--
Loop-equivariance data for already constructed path-class continuation.

This separates the path-continuation/path-independence part of the boundary
from the monodromy assertion that loop precomposition acts by a real Mobius
holonomy lift.
-/
structure PathClassAnalyticContinuationEquivarianceData
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (pathClassContinuation :
      PathClassAnalyticContinuationData x₀ g localModels) where
  /-- Lifted real holonomy obtained from monodromy around loops. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Loop action on path classes matches the lifted real Mobius action on values. -/
  pathClass_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (x : X)
      (q : Path.Homotopic.Quotient x₀ x),
      pathClassContinuation.valueAt x
          (Path.Homotopic.Quotient.trans (FundamentalGroup.toPath γ⁻¹) q) =
        holonomyLift.upperHalfPlaneAction γ
          (pathClassContinuation.valueAt x q)

namespace PathClassAnalyticContinuationEquivarianceData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    {C : PathClassAnalyticContinuationData x₀ g localModels}

/--
Path-class continuation data together with loop equivariance give the
path-class monodromy package.
-/
def toPathClassAnalyticContinuationMonodromyData
    (E : PathClassAnalyticContinuationEquivarianceData C) :
    PathClassAnalyticContinuationMonodromyData x₀ g localModels where
  pathClassContinuation := C
  holonomyLift := E.holonomyLift
  pathClass_equivariant := E.pathClass_equivariant

end PathClassAnalyticContinuationEquivarianceData

/--
Monodromy data for finite-chain terminal continuation with value-level
homotopy descent.

This weakens `PathChainTerminalBranchAnalyticContinuationMonodromyData` by not
requiring exact homotopy invariance of the auxiliary terminal chart, Mobius
representative, or sheet neighborhood choices.
-/
structure PathChainTerminalBranchAnalyticContinuationValueMonodromyData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelAtlas X g) where
  /-- Value-level finite-chain terminal continuation data. -/
  chainTerminalContinuation :
    PathChainTerminalBranchAnalyticContinuationValueData x₀ g localModels
  /-- Lifted real holonomy obtained from loop monodromy. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Loop-precomposition of paths gives the lifted Mobius action on chain values. -/
  chain_terminal_path_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x),
      Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
      chainTerminalContinuation.terminalValue (loop.trans p) =
        holonomyLift.upperHalfPlaneAction γ
          (chainTerminalContinuation.terminalValue p)

/--
Loop-equivariance data for already constructed value-level finite-chain
terminal continuation.

This separates the construction of terminal values along paths from the
monodromy assertion that loop precomposition acts by a real Mobius holonomy
lift.
-/
structure PathChainTerminalBranchAnalyticContinuationValueEquivarianceData
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    (chainTerminalContinuation :
      PathChainTerminalBranchAnalyticContinuationValueData
        x₀ g localModels) where
  /-- Lifted real holonomy obtained from loop monodromy. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Loop-precomposition of paths gives the lifted Mobius action on chain values. -/
  chain_terminal_path_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x),
      Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
      chainTerminalContinuation.terminalValue (loop.trans p) =
        holonomyLift.upperHalfPlaneAction γ
          (chainTerminalContinuation.terminalValue p)

namespace PathChainTerminalBranchAnalyticContinuationValueEquivarianceData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    {C : PathChainTerminalBranchAnalyticContinuationValueData x₀ g localModels}

/--
Terminal value data together with loop equivariance give the value-level
finite-chain monodromy package.
-/
def toPathChainTerminalBranchAnalyticContinuationValueMonodromyData
    (E :
      PathChainTerminalBranchAnalyticContinuationValueEquivarianceData C) :
    PathChainTerminalBranchAnalyticContinuationValueMonodromyData
      x₀ g localModels where
  chainTerminalContinuation := C
  holonomyLift := E.holonomyLift
  chain_terminal_path_equivariant := E.chain_terminal_path_equivariant

end PathChainTerminalBranchAnalyticContinuationValueEquivarianceData

namespace PathChainTerminalBranchAnalyticContinuationValueMonodromyData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/--
Value-level finite-chain terminal monodromy data descend directly to
path-class monodromy data.  Auxiliary branch choices are taken from a chosen
representative of each path class; only values are quotient-invariant.
-/
noncomputable def toPathClassAnalyticContinuationMonodromyData
    (M :
      PathChainTerminalBranchAnalyticContinuationValueMonodromyData
        x₀ g localModels) :
    PathClassAnalyticContinuationMonodromyData x₀ g localModels where
  pathClassContinuation :=
    M.chainTerminalContinuation.toPathClassAnalyticContinuationData
  holonomyLift := M.holonomyLift
  pathClass_equivariant := by
    intro γ x q
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        induction hloop : FundamentalGroup.toPath γ⁻¹ using
          Path.Homotopic.Quotient.ind with
        | mk loop =>
            rw [← Path.Homotopic.Quotient.mk_trans]
            change
              M.chainTerminalContinuation.terminalValueAt x
                  (Path.Homotopic.Quotient.mk (loop.trans p)) =
                M.holonomyLift.upperHalfPlaneAction γ
                  (M.chainTerminalContinuation.terminalValueAt x
                    (Path.Homotopic.Quotient.mk p))
            rw [PathChainTerminalBranchAnalyticContinuationValueData.terminalValueAt_mk,
              PathChainTerminalBranchAnalyticContinuationValueData.terminalValueAt_mk]
            exact M.chain_terminal_path_equivariant γ loop p hloop.symm

/--
Value-level finite-chain terminal monodromy data give the cover-level
monodromy boundary after quotienting through path classes.
-/
noncomputable def toAnalyticContinuationMonodromyData
    (M :
      PathChainTerminalBranchAnalyticContinuationValueMonodromyData
        x₀ g localModels) :
    AnalyticContinuationMonodromyData x₀ g localModels :=
  M.toPathClassAnalyticContinuationMonodromyData.toAnalyticContinuationMonodromyData

end PathChainTerminalBranchAnalyticContinuationValueMonodromyData

namespace PathChainTerminalBranchAnalyticContinuationMonodromyData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/--
Strong finite-chain terminal monodromy data give the weaker value-level
monodromy package by forgetting literal invariance of auxiliary branch choices.
-/
def toPathChainTerminalBranchAnalyticContinuationValueMonodromyData
    (M :
      PathChainTerminalBranchAnalyticContinuationMonodromyData
        x₀ g localModels) :
    PathChainTerminalBranchAnalyticContinuationValueMonodromyData
      x₀ g localModels where
  chainTerminalContinuation :=
    M.chainTerminalContinuation.toPathChainTerminalBranchAnalyticContinuationValueData
  holonomyLift := M.holonomyLift
  chain_terminal_path_equivariant := by
    intro γ loop x p hloop
    exact M.chain_terminal_path_equivariant γ loop p hloop

end PathChainTerminalBranchAnalyticContinuationMonodromyData

namespace PathTerminalBranchAnalyticContinuationMonodromyData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/--
Terminal-branch monodromy data descend directly to path-class monodromy data.
The terminal-value formula is preserved through the quotient.
-/
def toPathClassAnalyticContinuationMonodromyData
    (M :
      PathTerminalBranchAnalyticContinuationMonodromyData
        x₀ g localModels) :
    PathClassAnalyticContinuationMonodromyData x₀ g localModels where
  pathClassContinuation :=
    M.terminalContinuation.toPathClassAnalyticContinuationData
  holonomyLift := M.holonomyLift
  pathClass_equivariant := by
    intro γ x q
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        induction hloop : FundamentalGroup.toPath γ⁻¹ using
          Path.Homotopic.Quotient.ind with
        | mk loop =>
            simpa [
              PathTerminalBranchAnalyticContinuationData.toPathClassAnalyticContinuationData,
              PathTerminalBranchAnalyticContinuationData.terminalValueAt,
              ← Path.Homotopic.Quotient.mk_trans] using
              M.terminal_path_equivariant γ loop p hloop.symm

/--
Terminal-branch monodromy data give the cover-level monodromy boundary
directly after quotienting through path classes.
-/
def toAnalyticContinuationMonodromyData
    (M :
      PathTerminalBranchAnalyticContinuationMonodromyData
        x₀ g localModels) :
    AnalyticContinuationMonodromyData x₀ g localModels :=
  M.toPathClassAnalyticContinuationMonodromyData.toAnalyticContinuationMonodromyData

end PathTerminalBranchAnalyticContinuationMonodromyData

namespace PathChainTerminalBranchAnalyticContinuationMonodromyData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/--
Finite-chain terminal monodromy data descend directly to path-class monodromy
data.  The proof quotients the loop-precomposition equivariance through the
path-homotopy class relation.
-/
def toPathClassAnalyticContinuationMonodromyData
    (M :
      PathChainTerminalBranchAnalyticContinuationMonodromyData
        x₀ g localModels) :
    PathClassAnalyticContinuationMonodromyData x₀ g localModels where
  pathClassContinuation :=
    M.chainTerminalContinuation.toPathClassAnalyticContinuationData
  holonomyLift := M.holonomyLift
  pathClass_equivariant := by
    intro γ x q
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        induction hloop : FundamentalGroup.toPath γ⁻¹ using
          Path.Homotopic.Quotient.ind with
        | mk loop =>
            simpa [
              PathChainTerminalBranchAnalyticContinuationData.toPathClassAnalyticContinuationData,
              PathChainTerminalBranchAnalyticContinuationData.terminalValueAt,
              ← Path.Homotopic.Quotient.mk_trans] using
              M.chain_terminal_path_equivariant γ loop p hloop.symm

/--
Finite-chain terminal monodromy data give the cover-level monodromy boundary
directly after quotienting through path classes.
-/
def toAnalyticContinuationMonodromyData
    (M :
      PathChainTerminalBranchAnalyticContinuationMonodromyData
        x₀ g localModels) :
    AnalyticContinuationMonodromyData x₀ g localModels :=
  M.toPathClassAnalyticContinuationMonodromyData.toAnalyticContinuationMonodromyData

end PathChainTerminalBranchAnalyticContinuationMonodromyData

namespace PathAnalyticContinuationMonodromyData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}

/-- Actual-path monodromy data descend to path-class monodromy data. -/
def toPathClassAnalyticContinuationMonodromyData
    (M : PathAnalyticContinuationMonodromyData x₀ g localModels) :
    PathClassAnalyticContinuationMonodromyData x₀ g localModels where
  pathClassContinuation :=
    M.pathContinuation.toPathClassAnalyticContinuationData
  holonomyLift := M.holonomyLift
  pathClass_equivariant := by
    intro γ x q
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        induction hloop : FundamentalGroup.toPath γ⁻¹ using
          Path.Homotopic.Quotient.ind with
        | mk loop =>
            simpa [PathAnalyticContinuationData.valueAt,
              PathAnalyticContinuationData.toPathClassAnalyticContinuationData,
              ← Path.Homotopic.Quotient.mk_trans] using
              M.path_equivariant γ loop p hloop.symm

end PathAnalyticContinuationMonodromyData

end HyperbolicMetric

end

end JJMath
