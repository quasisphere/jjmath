import JJMath.Hyperbolic.Converse.Continuation.SamePathComparison

/-!
# Split analytic continuation targets for the partial converse
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

namespace PathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- Coherent terminal-sheet homotopy data fill the agreement record. -/
noncomputable def toCanonicalSheetAgreementData
    (D :
      PathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
      x₀ g localModels where
  basedWeakHandoffAlong := D.basedWeakHandoffAlong
  terminalValue_eq_on_terminalSheet := by
    intro x p y' p' hy' hclass
    exact
      D.terminalSheetHomotopyPrinciple p y' hy' p'
        (PathLocalTransitionModelBasedWeakHandoffSkeleton.homotopic_to_path_trans_terminalSheetPathInSet_of_mk_eq_pathClass
          (D.basedWeakHandoffAlong p) hy' hclass)

end PathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyData

/--
Coherent finite-grid/local-extension data for based weak handoff continuation.

This is the more construction-oriented boundary: choose the skeletons, prove
finite grid walks for endpoint-fixed homotopies, and prove compatibility with
local extension inside terminal sheets.
-/
structure PathLocalTransitionBasedWeakHandoffHomotopyGridLocalExtensionData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Chosen based weak handoff skeletons along representative paths. -/
  basedWeakHandoffAlong :
    ∀ {x : X} (p : Path x₀ x),
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p
  /-- Finite homotopy-grid walks for the chosen skeletons. -/
  homotopyGridWalk :
    PathLocalTransitionBasedWeakHandoffHomotopyGridWalkPrinciple
      x₀ g localModels basedWeakHandoffAlong
  /-- Local-extension compatibility for terminal sheets. -/
  terminalSheetLocalExtension :
    PathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple
      x₀ g localModels basedWeakHandoffAlong

namespace PathLocalTransitionBasedWeakHandoffHomotopyGridLocalExtensionData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Finite-grid/local-extension data give coherent terminal-sheet homotopy data.
-/
def toTerminalSheetHomotopyData
    (D :
      PathLocalTransitionBasedWeakHandoffHomotopyGridLocalExtensionData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyData
      x₀ g localModels where
  basedWeakHandoffAlong := D.basedWeakHandoffAlong
  terminalSheetHomotopyPrinciple :=
    pathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyPrinciple_of_homotopyGridWalk_and_localExtension
      D.basedWeakHandoffAlong D.homotopyGridWalk D.terminalSheetLocalExtension

/-- Finite-grid/local-extension data fill the agreement record. -/
noncomputable def toCanonicalSheetAgreementData
    (D :
      PathLocalTransitionBasedWeakHandoffHomotopyGridLocalExtensionData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
      x₀ g localModels :=
  D.toTerminalSheetHomotopyData.toCanonicalSheetAgreementData

end PathLocalTransitionBasedWeakHandoffHomotopyGridLocalExtensionData

/--
Coherent elementary-grid/local-extension data for based weak handoff
continuation.

This is a sharper construction boundary than `HomotopyGridLocalExtensionData`:
the finite grid walk is required to be built from explicit elementary grid
moves.
-/
structure PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Chosen based weak handoff skeletons along representative paths. -/
  basedWeakHandoffAlong :
    ∀ {x : X} (p : Path x₀ x),
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p
  /-- Finite elementary-grid walks for endpoint-fixed homotopies. -/
  elementaryGridMoveWalk :
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalkPrinciple
      x₀ g localModels basedWeakHandoffAlong
  /-- Local-extension compatibility for terminal sheets. -/
  terminalSheetLocalExtension :
    PathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple
      x₀ g localModels basedWeakHandoffAlong

namespace PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Elementary-grid/local-extension data give the coarser finite-grid/local-extension
data.
-/
def toHomotopyGridLocalExtensionData
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffHomotopyGridLocalExtensionData
      x₀ g localModels where
  basedWeakHandoffAlong := D.basedWeakHandoffAlong
  homotopyGridWalk :=
    pathLocalTransitionBasedWeakHandoffHomotopyGridWalkPrinciple_of_elementaryGridMoveWalkPrinciple
      D.elementaryGridMoveWalk
  terminalSheetLocalExtension := D.terminalSheetLocalExtension

/--
Elementary-grid/local-extension data give coherent terminal-sheet homotopy
data.
-/
def toTerminalSheetHomotopyData
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyData
      x₀ g localModels :=
  D.toHomotopyGridLocalExtensionData.toTerminalSheetHomotopyData

/-- Elementary-grid/local-extension data fill the agreement record. -/
noncomputable def toCanonicalSheetAgreementData
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
      x₀ g localModels :=
  D.toHomotopyGridLocalExtensionData.toCanonicalSheetAgreementData

end PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionData

/--
Coherent elementary-grid/terminal-extension-agreement data.

This is a sharper form of `ElementaryGridLocalExtensionData`: instead of
asking directly for terminal branch equality after local extension, it asks
for the concrete terminal-center and terminal-Mobius agreement that produces
that equality.
-/
structure PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Chosen based weak handoff skeletons along representative paths. -/
  basedWeakHandoffAlong :
    ∀ {x : X} (p : Path x₀ x),
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p
  /-- Finite elementary-grid walks for endpoint-fixed homotopies. -/
  elementaryGridMoveWalk :
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalkPrinciple
      x₀ g localModels basedWeakHandoffAlong
  /-- Terminal-sheet extension keeps terminal chart and terminal Mobius data. -/
  terminalSheetExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
      x₀ g localModels basedWeakHandoffAlong

/--
Coherent elementary-grid/PSL-terminal-extension-agreement data.

This is the projective-strength analogue of
`PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData`: the
terminal chart is fixed under terminal-sheet extension, and the accumulated
Mobius representative is fixed only after projection to PSL.
-/
structure PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- Chosen based weak handoff skeletons along representative paths. -/
  basedWeakHandoffAlong :
    ∀ {x : X} (p : Path x₀ x),
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p
  /-- Finite elementary-grid walks for endpoint-fixed homotopies. -/
  elementaryGridMoveWalk :
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalkPrinciple
      x₀ g localModels basedWeakHandoffAlong
  /-- Terminal-sheet extension keeps terminal chart and terminal Mobius PSL class. -/
  terminalSheetExtensionProjectionAgreement :
    PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionProjectionAgreementPrinciple
      x₀ g localModels basedWeakHandoffAlong

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- Exact terminal-extension agreement data forget to PSL-level agreement data. -/
def toElementaryGridExtensionProjectionAgreementData
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData
      x₀ g localModels where
  basedWeakHandoffAlong := D.basedWeakHandoffAlong
  elementaryGridMoveWalk := D.elementaryGridMoveWalk
  terminalSheetExtensionProjectionAgreement :=
    pathLocalTransitionBasedWeakHandoffTerminalSheetExtensionProjectionAgreementPrinciple_of_extensionAgreement
      D.terminalSheetExtensionAgreement

/--
Terminal-extension agreement gives coherent elementary-grid/local-extension
data.
-/
def toElementaryGridLocalExtensionData
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionData
      x₀ g localModels where
  basedWeakHandoffAlong := D.basedWeakHandoffAlong
  elementaryGridMoveWalk := D.elementaryGridMoveWalk
  terminalSheetLocalExtension :=
    pathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple_of_terminalSheetExtensionAgreement
      D.terminalSheetExtensionAgreement

/--
Terminal-extension agreement gives coherent finite-grid/local-extension data.
-/
def toHomotopyGridLocalExtensionData
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffHomotopyGridLocalExtensionData
      x₀ g localModels :=
  D.toElementaryGridLocalExtensionData.toHomotopyGridLocalExtensionData

/--
Terminal-extension agreement gives coherent terminal-sheet homotopy data.
-/
def toTerminalSheetHomotopyData
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyData
      x₀ g localModels :=
  D.toElementaryGridLocalExtensionData.toTerminalSheetHomotopyData

/-- Terminal-extension agreement data fill the agreement record. -/
noncomputable def toCanonicalSheetAgreementData
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
      x₀ g localModels :=
  D.toElementaryGridLocalExtensionData.toCanonicalSheetAgreementData

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
PSL terminal-extension agreement gives coherent elementary-grid/local-extension
data.
-/
def toElementaryGridLocalExtensionData
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffElementaryGridLocalExtensionData
      x₀ g localModels where
  basedWeakHandoffAlong := D.basedWeakHandoffAlong
  elementaryGridMoveWalk := D.elementaryGridMoveWalk
  terminalSheetLocalExtension :=
    pathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple_of_terminalSheetExtensionProjectionAgreement
      D.terminalSheetExtensionProjectionAgreement

/--
PSL terminal-extension agreement gives coherent finite-grid/local-extension
data.
-/
def toHomotopyGridLocalExtensionData
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffHomotopyGridLocalExtensionData
      x₀ g localModels :=
  D.toElementaryGridLocalExtensionData.toHomotopyGridLocalExtensionData

/--
PSL terminal-extension agreement gives coherent terminal-sheet homotopy data.
-/
def toTerminalSheetHomotopyData
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyData
      x₀ g localModels :=
  D.toElementaryGridLocalExtensionData.toTerminalSheetHomotopyData

/-- PSL terminal-extension agreement data fill the agreement record. -/
noncomputable def toCanonicalSheetAgreementData
    (D :
      PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
      x₀ g localModels :=
  D.toElementaryGridLocalExtensionData.toCanonicalSheetAgreementData

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData

/--
The terminal-sheet homotopy principle fills the agreement record.  The only
cover-theoretic input is that a point in a terminal sheet is represented by
the continued path followed by the canonical local path in that sheet.
-/
noncomputable def pathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData_of_terminalSheetHomotopyPrinciple
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (hPrinciple :
      PathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyPrinciple
        x₀ g localModels basedWeakHandoffAlong) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
      x₀ g localModels where
  basedWeakHandoffAlong := basedWeakHandoffAlong
  terminalValue_eq_on_terminalSheet := by
    intro x p y' p' hy' hclass
    exact
      hPrinciple p y' hy' p'
        (PathLocalTransitionModelBasedWeakHandoffSkeleton.homotopic_to_path_trans_terminalSheetPathInSet_of_mk_eq_pathClass
          (basedWeakHandoffAlong p) hy' hclass)

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Canonical-terminal-sheet value continuation forgets to terminal-sheet
agreement; homotopy descent is no longer an input on the weaker side.
-/
noncomputable def toCanonicalSheetAgreementData
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
      x₀ g localModels where
  basedWeakHandoffAlong := C.basedWeakHandoffAlong
  terminalValue_eq_on_terminalSheet := C.terminalValue_eq_on_terminalSheet

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData

/--
Single-valued PSL continuation on the canonical cover for based weak handoff
terminal sheets.

This is the universal-cover version of the continuation boundary: instead of
postulating value descent for homotopic paths directly, it stores one
single-valued map `dev` upstairs and requires each terminal sheet formula to
agree with that map.  Homotopy descent then follows because homotopic paths
represent the same point of the canonical cover.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) where
  /-- A based weak handoff skeleton along each representative path. -/
  basedWeakHandoffAlong :
    ∀ {x : X} (p : Path x₀ x),
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p
  /-- The single-valued continued map on the canonical cover. -/
  dev : (canonicalContinuationCover x₀).total → ℍ
  /-- PSL-valued real holonomy. -/
  holonomy : RealHolonomyRepresentation X x₀
  /-- Each terminal sheet formula agrees with the single-valued upstairs map. -/
  dev_eq_on_terminalSheet :
    ∀ {x : X} (p : Path x₀ x) (y' : PathHomotopyUniversalCover X x₀),
      y' ∈ (basedWeakHandoffAlong p).terminalSheet →
      dev y' =
        realMobiusRepresentativeAction
          ((basedWeakHandoffAlong p).terminalMobius)
          ((localModels.chartAt
              ((basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y'))
  /-- Deck transformations act through the PSL holonomy on the upstairs map. -/
  dev_equivariant :
    ∀ (γ : FundamentalGroup X x₀)
      (y : (canonicalContinuationCover x₀).total),
      dev ((canonicalContinuationCover x₀).deckAction γ y) =
        holonomy.upperHalfPlaneAction γ (dev y)

namespace PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/-- At the represented terminal point, the terminal branch value is `dev`. -/
theorem terminalValue_eq_dev_terminalCoverPoint
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
        x₀ g localModels)
    {x : X} (p : Path x₀ x) :
    (C.basedWeakHandoffAlong p).terminalValue =
      C.dev (C.basedWeakHandoffAlong p).terminalCoverPoint := by
  have h :=
    C.dev_eq_on_terminalSheet p
      (C.basedWeakHandoffAlong p).terminalCoverPoint
      (C.basedWeakHandoffAlong p).terminalCoverPoint_mem_terminalSheet
  simpa [PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalValue,
    PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalCoverPoint] using
    h.symm

/--
The single-valued upstairs map turns endpoint-fixed homotopy of paths into
equality of terminal branch values.
-/
theorem terminalValue_homotopic
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
        x₀ g localModels)
    {x : X} {p q : Path x₀ x} (hpq : Path.Homotopic p q) :
    (C.basedWeakHandoffAlong p).terminalValue =
      (C.basedWeakHandoffAlong q).terminalValue := by
  rw [C.terminalValue_eq_dev_terminalCoverPoint p,
    C.terminalValue_eq_dev_terminalCoverPoint q]
  rw [(C.basedWeakHandoffAlong p).terminalCoverPoint_eq_of_homotopic
    (C.basedWeakHandoffAlong q) hpq]

/--
If a path represents the path class of a point in a terminal sheet, its
terminal formula is the same upstairs value as the terminal sheet formula.
-/
theorem terminalValue_eq_on_terminalSheet
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
        x₀ g localModels)
    {x : X} (p : Path x₀ x) (y' : PathHomotopyUniversalCover X x₀)
    (p' : Path x₀ (PathHomotopyUniversalCover.endpoint y'))
    (hy' : y' ∈ (C.basedWeakHandoffAlong p).terminalSheet)
    (hclass :
      Path.Homotopic.Quotient.mk p' =
        PathHomotopyUniversalCover.pathClass y') :
    realMobiusRepresentativeAction ((C.basedWeakHandoffAlong p').terminalMobius)
        ((localModels.chartAt
            ((C.basedWeakHandoffAlong p').terminalCenter)).toUpperHalfPlane
          (PathHomotopyUniversalCover.endpoint y')) =
      realMobiusRepresentativeAction ((C.basedWeakHandoffAlong p).terminalMobius)
        ((localModels.chartAt
            ((C.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
          (PathHomotopyUniversalCover.endpoint y')) := by
  have hp'_point :
      (C.basedWeakHandoffAlong p').terminalCoverPoint = y' :=
    (C.basedWeakHandoffAlong p').terminalCoverPoint_eq_of_mk_eq_pathClass
      hclass
  have hp'_mem : y' ∈ (C.basedWeakHandoffAlong p').terminalSheet := by
    simpa [hp'_point] using
      (C.basedWeakHandoffAlong p').terminalCoverPoint_mem_terminalSheet
  have hp_dev := C.dev_eq_on_terminalSheet p y' hy'
  have hp'_dev := C.dev_eq_on_terminalSheet p' y' hp'_mem
  exact hp'_dev.symm.trans hp_dev

/--
Cover-level PSL continuation gives canonical-terminal-sheet value
continuation.
-/
noncomputable def toCanonicalSheetAnalyticContinuationValueData
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData
      x₀ g localModels where
  basedWeakHandoffAlong := C.basedWeakHandoffAlong
  terminalValue_homotopic := by
    intro x p q hpq
    exact C.terminalValue_homotopic hpq
  terminalValue_eq_on_terminalSheet := by
    intro x p y' p' hy' hclass
    exact C.terminalValue_eq_on_terminalSheet p y' p' hy' hclass

/--
Cover-level PSL continuation forgets to canonical terminal-sheet agreement
data.  The homotopy descent field of value-continuation data is not needed
here; terminal-sheet agreement is exactly the local formula compatibility.
-/
noncomputable def toCanonicalSheetAgreementData
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
      x₀ g localModels where
  basedWeakHandoffAlong := C.basedWeakHandoffAlong
  terminalValue_eq_on_terminalSheet := by
    intro x p y' p' hy' hclass
    exact C.terminalValue_eq_on_terminalSheet p y' p' hy' hclass

end PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL

/--
PSL loop-equivariance data for canonical-terminal-sheet agreement.

This is weaker than storing deck equivariance of the constructed upstairs map:
deck equivariance is derived by evaluating the map on representative path
classes and using terminal-sheet descent.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- PSL-valued real holonomy obtained from loop monodromy. -/
  holonomy : RealHolonomyRepresentation X x₀
  /-- Loop-precomposition of paths gives the PSL action on terminal values. -/
  terminal_path_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x),
      Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
      agreementContinuation.terminalValue (loop.trans p) =
        holonomy.upperHalfPlaneAction γ
          (agreementContinuation.terminalValue p)

/--
Terminal-Mobius PSL covariance data for canonical-terminal-sheet agreement.

This is a more concrete monodromy boundary than value equivariance: it records
that loop precomposition preserves the terminal chart and multiplies the
terminal PSL class by the loop holonomy.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- PSL-valued real holonomy obtained from loop monodromy. -/
  holonomy : RealHolonomyRepresentation X x₀
  /-- Loop-precomposition preserves the terminal chart used by the branch. -/
  terminalCenter_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x),
      Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
      (agreementContinuation.basedWeakHandoffAlong (loop.trans p)).terminalCenter =
        (agreementContinuation.basedWeakHandoffAlong p).terminalCenter
  /-- Loop-precomposition multiplies terminal Mobius classes by PSL holonomy. -/
  terminalProjection_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x),
      Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
      realMobiusProjection
          ((agreementContinuation.basedWeakHandoffAlong (loop.trans p)).terminalMobius) =
        holonomy γ *
          realMobiusProjection
            ((agreementContinuation.basedWeakHandoffAlong p).terminalMobius)

/--
Transition-adjusted terminal-Mobius PSL covariance data for
canonical-terminal-sheet agreement.

Unlike `PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceDataPSL`,
this does not require loop-precomposition to preserve the selected terminal
chart.  It compares terminal Mobius classes after inserting the real-Mobius
transition between the two terminal local models at the endpoint.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- PSL-valued real holonomy obtained from loop monodromy. -/
  holonomy : RealHolonomyRepresentation X x₀
  /-- The endpoint transition from the old terminal chart to the loop-prepended one. -/
  terminalTransitionRepresentative :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (_p : Path x₀ x),
      Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
      RealMobiusRepresentative
  /-- The chosen endpoint transition really identifies the two terminal charts at the endpoint. -/
  terminalTransitionAtEndpoint :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x)
      (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
      (localModels.chartAt
          ((agreementContinuation.basedWeakHandoffAlong (loop.trans p)).terminalCenter)).toUpperHalfPlane x =
        realMobiusRepresentativeAction
          (terminalTransitionRepresentative γ loop p hloop)
          ((localModels.chartAt
              ((agreementContinuation.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane x)
  /-- Loop-precomposition multiplies the adjusted terminal Mobius classes by PSL holonomy. -/
  terminalTransitionProjection_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x)
      (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
      realMobiusProjection
          (((agreementContinuation.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            terminalTransitionRepresentative γ loop p hloop) =
        holonomy γ *
          realMobiusProjection
            ((agreementContinuation.basedWeakHandoffAlong p).terminalMobius)

/--
Terminal-Mobius PSL covariance data using the automatic endpoint chart
transition supplied by the local-transition atlas.

This removes the non-mathematical burden of providing the endpoint transition
and leaves only the actual monodromy equality.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- PSL-valued real holonomy obtained from loop monodromy. -/
  holonomy : RealHolonomyRepresentation X x₀
  /--
  Loop-precomposition multiplies the terminal Mobius class, adjusted by the
  automatically selected endpoint chart transition, by PSL holonomy.
  -/
  automaticTerminalTransitionProjection_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x)
      (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
      realMobiusProjection
          (((agreementContinuation.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            agreementContinuation.terminalTransitionRepresentative γ loop p hloop) =
        holonomy γ *
          realMobiusProjection
            ((agreementContinuation.basedWeakHandoffAlong p).terminalMobius)

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
The canonical representative loop used to read off loop monodromy from
terminal continuation.  The convention matches deck actions in this file:
loop-prepending represents `γ⁻¹` at the path-class level.
-/
noncomputable def canonicalLoopFor
    (_C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) : Path x₀ x₀ :=
  Quot.out (FundamentalGroup.toPath γ⁻¹)

/-- The canonical representative loop has the required path class. -/
theorem canonicalLoopFor_spec
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) :
    Path.Homotopic.Quotient.mk (C.canonicalLoopFor γ) =
      FundamentalGroup.toPath γ⁻¹ :=
  Quot.out_eq (FundamentalGroup.toPath γ⁻¹)

/--
For the canonical loop representative, deck action sends the terminal cover
point of `p` to the terminal cover point of the loop-prepended path.
-/
theorem deckAction_terminalCoverPoint_canonicalLoopFor
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x) :
    PathHomotopyUniversalCover.deckAction γ
        ((C.basedWeakHandoffAlong p).terminalCoverPoint) =
      (C.basedWeakHandoffAlong ((C.canonicalLoopFor γ).trans p)).terminalCoverPoint := by
  let S := C.basedWeakHandoffAlong p
  let T := C.basedWeakHandoffAlong ((C.canonicalLoopFor γ).trans p)
  have h :
      T.terminalCoverPoint =
        (canonicalContinuationCover x₀).deckAction γ S.terminalCoverPoint :=
    PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalCoverPoint_loopTrans_eq_deckAction
      γ (C.canonicalLoopFor γ) S T (C.canonicalLoopFor_spec γ)
  simpa [S, T, canonicalContinuationCover, SimplyConnectedCover.deckAction,
    PathHomotopyUniversalCover.deckHomeomorphism_apply] using h.symm

/--
The source terminal cover point lies in the deck-preimage of the canonical
loop-prepended terminal sheet.
-/
theorem terminalCoverPoint_mem_deck_preimage_canonicalLoop_terminalSheet
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x) :
    (C.basedWeakHandoffAlong p).terminalCoverPoint ∈
      (PathHomotopyUniversalCover.deckAction γ) ⁻¹'
        (C.basedWeakHandoffAlong ((C.canonicalLoopFor γ).trans p)).terminalSheet := by
  simpa [C.deckAction_terminalCoverPoint_canonicalLoopFor γ p] using
    (C.basedWeakHandoffAlong
      ((C.canonicalLoopFor γ).trans p)).terminalCoverPoint_mem_terminalSheet

/-- The base path used to normalize terminal Mobius products. -/
def baseNormalizationPath
    (_C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) : Path x₀ x₀ :=
  Path.refl x₀

/-- The terminal PSL class of the normalized base path. -/
noncomputable def baseTerminalProjection
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) : RealMobiusGroup :=
  realMobiusProjection
    ((C.basedWeakHandoffAlong C.baseNormalizationPath).terminalMobius)

/--
The adjusted terminal PSL class obtained by continuing around the canonical
representative of `γ⁻¹` and then back along the base normalization path.
-/
noncomputable def loopAdjustedTerminalProjection
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) : RealMobiusGroup :=
  realMobiusProjection
    (((C.basedWeakHandoffAlong
        ((C.canonicalLoopFor γ).trans C.baseNormalizationPath)).terminalMobius) *
      C.terminalTransitionRepresentative γ (C.canonicalLoopFor γ)
        (x := x₀) C.baseNormalizationPath (C.canonicalLoopFor_spec γ))

/--
The PSL holonomy candidate read off from loop terminal continuation, normalized
by the base terminal class.
-/
noncomputable def derivedHolonomyProjection
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) : RealMobiusGroup :=
  C.loopAdjustedTerminalProjection γ * (C.baseTerminalProjection)⁻¹

/--
The defining loop terminal class equals the derived holonomy times the base
terminal class.
-/
theorem loopAdjustedTerminalProjection_eq_derivedHolonomyProjection_mul_base
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) :
    C.loopAdjustedTerminalProjection γ =
      C.derivedHolonomyProjection γ * C.baseTerminalProjection := by
  simp [derivedHolonomyProjection, mul_assoc]

/--
Canonical-loop covariance is automatic at the base normalization path.

Thus the remaining canonical-loop covariance boundary is propagation of this
base loop-terminal class along arbitrary terminal paths.
-/
theorem canonicalLoopTransitionProjection_equivariant_baseNormalizationPath
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) :
    realMobiusProjection
        (((C.basedWeakHandoffAlong
            ((C.canonicalLoopFor γ).trans C.baseNormalizationPath)).terminalMobius) *
          C.terminalTransitionRepresentativeBetween C.baseNormalizationPath
            ((C.canonicalLoopFor γ).trans C.baseNormalizationPath)) =
      C.derivedHolonomyProjection γ *
        realMobiusProjection
          ((C.basedWeakHandoffAlong C.baseNormalizationPath).terminalMobius) := by
  have hBetween :=
    C.terminalTransitionRepresentative_projection_eq_between
      γ (C.canonicalLoopFor γ) (x := x₀) C.baseNormalizationPath
      (C.canonicalLoopFor_spec γ)
  have hOldBetween :
      C.loopAdjustedTerminalProjection γ =
        realMobiusProjection
          (((C.basedWeakHandoffAlong
              ((C.canonicalLoopFor γ).trans C.baseNormalizationPath)).terminalMobius) *
            C.terminalTransitionRepresentativeBetween C.baseNormalizationPath
              ((C.canonicalLoopFor γ).trans C.baseNormalizationPath)) := by
    rw [loopAdjustedTerminalProjection]
    let M :=
      (C.basedWeakHandoffAlong
        ((C.canonicalLoopFor γ).trans C.baseNormalizationPath)).terminalMobius
    calc
      realMobiusProjection
          (M * C.terminalTransitionRepresentative γ (C.canonicalLoopFor γ)
            (x := x₀) C.baseNormalizationPath (C.canonicalLoopFor_spec γ))
          = realMobiusProjection M *
              realMobiusProjection
                (C.terminalTransitionRepresentative γ (C.canonicalLoopFor γ)
                  (x := x₀) C.baseNormalizationPath (C.canonicalLoopFor_spec γ)) := by
            simp
      _ = realMobiusProjection M *
              realMobiusProjection
                (C.terminalTransitionRepresentativeBetween C.baseNormalizationPath
                  ((C.canonicalLoopFor γ).trans C.baseNormalizationPath)) := by
            rw [hBetween]
      _ =
        realMobiusProjection
          (M * C.terminalTransitionRepresentativeBetween C.baseNormalizationPath
            ((C.canonicalLoopFor γ).trans C.baseNormalizationPath)) := by
            simp
  rw [← hOldBetween]
  rw [C.loopAdjustedTerminalProjection_eq_derivedHolonomyProjection_mul_base γ]
  rfl

/--
The normalized canonical-loop terminal PSL class at a terminal path `p`.

This quotient removes the terminal Mobius class of `p`; the monodromy theorem
says that the resulting class is independent of `p` and hence equals its base
value.
-/
noncomputable def canonicalLoopNormalizedTerminalProjection
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x) :
    RealMobiusGroup :=
  realMobiusProjection
      (((C.basedWeakHandoffAlong ((C.canonicalLoopFor γ).trans p)).terminalMobius) *
        C.terminalTransitionRepresentativeBetween p ((C.canonicalLoopFor γ).trans p)) *
    (realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius))⁻¹

/--
At the base normalization path, the normalized canonical-loop terminal class
is exactly the derived holonomy.
-/
theorem canonicalLoopNormalizedTerminalProjection_baseNormalizationPath
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) :
    C.canonicalLoopNormalizedTerminalProjection γ C.baseNormalizationPath =
      C.derivedHolonomyProjection γ := by
  rw [canonicalLoopNormalizedTerminalProjection]
  rw [C.canonicalLoopTransitionProjection_equivariant_baseNormalizationPath γ]
  simp [mul_assoc]

/--
The normalized canonical-loop terminal class is invariant under changing the
endpoint path within its endpoint-fixed homotopy class.

This descends the remaining propagation problem from arbitrary path
representatives to points of the canonical cover.
-/
theorem canonicalLoopNormalizedTerminalProjection_homotopic
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀)
    {x : X} {p q : Path x₀ x} (hpq : Path.Homotopic p q) :
    C.canonicalLoopNormalizedTerminalProjection γ p =
      C.canonicalLoopNormalizedTerminalProjection γ q := by
  let L := C.canonicalLoopFor γ
  let Lp : Path x₀ x := L.trans p
  let Lq : Path x₀ x := L.trans q
  let Mp := (C.basedWeakHandoffAlong p).terminalMobius
  let Mq := (C.basedWeakHandoffAlong q).terminalMobius
  let MLp := (C.basedWeakHandoffAlong Lp).terminalMobius
  let MLq := (C.basedWeakHandoffAlong Lq).terminalMobius
  let Tpq := realMobiusProjection (C.terminalTransitionRepresentativeBetween p q)
  let Ap :=
    realMobiusProjection
      (MLp * C.terminalTransitionRepresentativeBetween p Lp)
  let Aq :=
    realMobiusProjection
      (MLq * C.terminalTransitionRepresentativeBetween q Lq)
  let Bp := realMobiusProjection Mp
  let Bq := realMobiusProjection Mq
  have hB :
      Bq * Tpq = Bp := by
    have h :=
      C.terminalTransitionRepresentativeBetween_adjusted_projection_eq_of_homotopic
        p q hpq
    simpa [Bq, Bp, Tpq, Mq] using h
  have hLoop : Path.Homotopic Lp Lq := by
    simpa [L, Lp, Lq] using (Path.Homotopic.refl L).hcomp hpq
  have hML :
      realMobiusProjection
          (MLq * C.terminalTransitionRepresentativeBetween Lp Lq) =
        realMobiusProjection MLp := by
    simpa [Lp, Lq, MLp, MLq] using
      C.terminalTransitionRepresentativeBetween_adjusted_projection_eq_of_homotopic
        Lp Lq hLoop
  have hA :
      Aq * Tpq = Ap := by
    have hViaQ :
        realMobiusProjection
            (MLq * C.terminalTransitionRepresentativeBetween p Lq) =
          realMobiusProjection
            ((MLq * C.terminalTransitionRepresentativeBetween q Lq) *
              C.terminalTransitionRepresentativeBetween p q) :=
      C.terminalTransitionRepresentativeBetween_adjusted_projection_trans
        p q Lq MLq
    have hViaLp :
        realMobiusProjection
            (MLq * C.terminalTransitionRepresentativeBetween p Lq) =
          realMobiusProjection
            ((MLq * C.terminalTransitionRepresentativeBetween Lp Lq) *
              C.terminalTransitionRepresentativeBetween p Lp) :=
      C.terminalTransitionRepresentativeBetween_adjusted_projection_trans
        p Lp Lq MLq
    calc
      Aq * Tpq
          =
        realMobiusProjection
          ((MLq * C.terminalTransitionRepresentativeBetween q Lq) *
            C.terminalTransitionRepresentativeBetween p q) := by
          simp [Aq, Tpq, mul_assoc]
      _ =
        realMobiusProjection
          (MLq * C.terminalTransitionRepresentativeBetween p Lq) := by
          rw [← hViaQ]
      _ =
        realMobiusProjection
          ((MLq * C.terminalTransitionRepresentativeBetween Lp Lq) *
            C.terminalTransitionRepresentativeBetween p Lp) := by
          rw [hViaLp]
      _ =
        realMobiusProjection
            (MLq * C.terminalTransitionRepresentativeBetween Lp Lq) *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween p Lp) := by
          simp
      _ =
        realMobiusProjection MLp *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween p Lp) := by
          rw [hML]
      _ = Ap := by
          simp [Ap]
  have hT : Tpq = Bq⁻¹ * Bp := by
    calc
      Tpq = 1 * Tpq := by simp
      _ = (Bq⁻¹ * Bq) * Tpq := by simp
      _ = Bq⁻¹ * (Bq * Tpq) := by simp
      _ = Bq⁻¹ * Bp := by rw [hB]
  have hTcancel : Tpq * Bp⁻¹ = Bq⁻¹ := by
    rw [hT]
    simp [mul_assoc]
  calc
    C.canonicalLoopNormalizedTerminalProjection γ p
        = Ap * Bp⁻¹ := by
        simp [canonicalLoopNormalizedTerminalProjection, L, Lp, Ap, Bp, Mp, MLp]
    _ = (Aq * Tpq) * Bp⁻¹ := by
        rw [hA]
    _ = Aq * (Tpq * Bp⁻¹) := by
        simp [mul_assoc]
    _ = Aq * Bq⁻¹ := by
        rw [hTcancel]
    _ = C.canonicalLoopNormalizedTerminalProjection γ q := by
        simp [canonicalLoopNormalizedTerminalProjection, L, Lq, Aq, Bq, Mq, MLq]

/--
The normalized canonical-loop terminal class as a function on the canonical
path-homotopy cover.
-/
noncomputable def canonicalLoopNormalizedProjectionAt
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀)
    (y : PathHomotopyUniversalCover X x₀) :
    RealMobiusGroup :=
  C.canonicalLoopNormalizedTerminalProjection γ
    (Quot.out (PathHomotopyUniversalCover.pathClass y))

/--
The cover-valued normalized projection agrees with the formula computed from
any representative path.
-/
theorem canonicalLoopNormalizedProjectionAt_mk
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀)
    {x : X} (p : Path x₀ x) :
    C.canonicalLoopNormalizedProjectionAt γ
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) =
      C.canonicalLoopNormalizedTerminalProjection γ p := by
  exact
    C.canonicalLoopNormalizedTerminalProjection_homotopic γ
      (PathLocalTransitionChainTerminalBranchAnalyticContinuationValueData.out_homotopic_mk p)

/--
At the distinguished base lift, the cover-valued normalized projection is the
derived holonomy.
-/
theorem canonicalLoopNormalizedProjectionAt_baseLift
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) :
    C.canonicalLoopNormalizedProjectionAt γ
        (PathHomotopyUniversalCover.baseLift x₀) =
      C.derivedHolonomyProjection γ := by
  simpa [PathHomotopyUniversalCover.baseLift,
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.baseNormalizationPath]
    using C.canonicalLoopNormalizedProjectionAt_mk γ C.baseNormalizationPath
      |>.trans (C.canonicalLoopNormalizedTerminalProjection_baseNormalizationPath γ)

/--
Constancy of the cover-valued normalized projection implies propagation of the
path-representative normalized projection from the base path.
-/
theorem canonicalLoopNormalizedProjection_propagates_from_base_of_const_on_cover
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (hConst :
      ∀ (γ : FundamentalGroup X x₀)
        (y : PathHomotopyUniversalCover X x₀),
        C.canonicalLoopNormalizedProjectionAt γ y =
          C.canonicalLoopNormalizedProjectionAt γ
            (PathHomotopyUniversalCover.baseLift x₀)) :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x),
      C.canonicalLoopNormalizedTerminalProjection γ p =
        C.canonicalLoopNormalizedTerminalProjection γ C.baseNormalizationPath := by
  intro γ x p
  calc
    C.canonicalLoopNormalizedTerminalProjection γ p
        =
      C.canonicalLoopNormalizedProjectionAt γ
        (⟨x, Path.Homotopic.Quotient.mk p⟩ :
          PathHomotopyUniversalCover X x₀) := by
        rw [C.canonicalLoopNormalizedProjectionAt_mk γ p]
    _ =
      C.canonicalLoopNormalizedProjectionAt γ
        (PathHomotopyUniversalCover.baseLift x₀) := by
        exact hConst γ _
    _ =
      C.canonicalLoopNormalizedTerminalProjection γ C.baseNormalizationPath := by
        rw [← C.canonicalLoopNormalizedProjectionAt_mk γ C.baseNormalizationPath]
        simp [PathHomotopyUniversalCover.baseLift,
          PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.baseNormalizationPath]

/--
If the normalized canonical-loop terminal class propagates unchanged from the
base path to every path, then canonical-loop covariance follows.
-/
theorem canonicalLoopTransitionProjection_equivariant_of_normalizedProjection_propagates_from_base
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (hProp :
      ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x),
        C.canonicalLoopNormalizedTerminalProjection γ p =
          C.canonicalLoopNormalizedTerminalProjection γ C.baseNormalizationPath) :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x),
      realMobiusProjection
          (((C.basedWeakHandoffAlong ((C.canonicalLoopFor γ).trans p)).terminalMobius) *
            C.terminalTransitionRepresentativeBetween p ((C.canonicalLoopFor γ).trans p)) =
        C.derivedHolonomyProjection γ *
          realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius) := by
  intro γ x p
  let A :=
    realMobiusProjection
      (((C.basedWeakHandoffAlong ((C.canonicalLoopFor γ).trans p)).terminalMobius) *
        C.terminalTransitionRepresentativeBetween p ((C.canonicalLoopFor γ).trans p))
  let B := realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius)
  have hNorm : A * B⁻¹ = C.derivedHolonomyProjection γ := by
    have h := hProp γ p
    rw [C.canonicalLoopNormalizedTerminalProjection_baseNormalizationPath γ] at h
    simpa [canonicalLoopNormalizedTerminalProjection, A, B] using h
  have hCancel := congrArg (fun T : RealMobiusGroup => T * B) hNorm
  simpa [A, B, mul_assoc] using hCancel

/--
Canonical-loop covariance implies arbitrary loop covariance, because the
transition-adjusted terminal class is invariant under changing the loop within
its endpoint-fixed homotopy class.
-/
theorem automaticTerminalTransitionProjection_equivariant_of_canonicalLoop_covariance
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (H : FundamentalGroup X x₀ → RealMobiusGroup)
    (hCanonical :
      ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x),
        realMobiusProjection
            (((C.basedWeakHandoffAlong ((C.canonicalLoopFor γ).trans p)).terminalMobius) *
              C.terminalTransitionRepresentativeBetween p
                ((C.canonicalLoopFor γ).trans p)) =
          H γ *
            realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius)) :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x)
      (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
      realMobiusProjection
          (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            C.terminalTransitionRepresentative γ loop p hloop) =
        H γ *
          realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius) := by
  intro γ loop x p hloop
  have hLoopHom :
      Path.Homotopic loop (C.canonicalLoopFor γ) := by
    apply Path.Homotopic.Quotient.eq.mp
    exact hloop.trans (C.canonicalLoopFor_spec γ).symm
  have hOldBetween :
      realMobiusProjection
          (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            C.terminalTransitionRepresentative γ loop p hloop) =
        realMobiusProjection
          (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            C.terminalTransitionRepresentativeBetween p (loop.trans p)) := by
    let M := (C.basedWeakHandoffAlong (loop.trans p)).terminalMobius
    have hBetween :=
      C.terminalTransitionRepresentative_projection_eq_between γ loop p hloop
    calc
      realMobiusProjection
          (M * C.terminalTransitionRepresentative γ loop p hloop)
          = realMobiusProjection M *
              realMobiusProjection
                (C.terminalTransitionRepresentative γ loop p hloop) := by
            simp
      _ = realMobiusProjection M *
              realMobiusProjection
                (C.terminalTransitionRepresentativeBetween p (loop.trans p)) := by
            rw [hBetween]
      _ =
        realMobiusProjection
          (M * C.terminalTransitionRepresentativeBetween p (loop.trans p)) := by
            simp
  rw [hOldBetween]
  rw [
    C.terminalTransitionRepresentativeBetween_loopTrans_adjusted_projection_eq_of_homotopic_loop
      loop (C.canonicalLoopFor γ) p hLoopHom]
  exact hCanonical γ p

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

/--
Automatic endpoint-transition terminal-Mobius covariance data with holonomy
derived from base-loop terminal continuation.

This exposes the true monodromy/cocycle boundary: prove that the loop terminal
classes descend to a multiplicative PSL representation and that arbitrary
path terminal classes transform by that derived representation.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- The derived loop-terminal assignment sends the identity loop class to `1`. -/
  derivedHolonomy_one :
    agreementContinuation.derivedHolonomyProjection
        (1 : FundamentalGroup X x₀) = 1
  /-- The derived loop-terminal assignment is multiplicative. -/
  derivedHolonomy_mul :
    ∀ γ δ : FundamentalGroup X x₀,
      agreementContinuation.derivedHolonomyProjection (γ * δ) =
        agreementContinuation.derivedHolonomyProjection γ *
          agreementContinuation.derivedHolonomyProjection δ
  /--
  Loop-precomposition multiplies arbitrary adjusted terminal Mobius classes by
  the derived loop-terminal holonomy.
  -/
  automaticTerminalTransitionProjection_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x)
      (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
      realMobiusProjection
          (((agreementContinuation.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            agreementContinuation.terminalTransitionRepresentative γ loop p hloop) =
        agreementContinuation.derivedHolonomyProjection γ *
          realMobiusProjection
            ((agreementContinuation.basedWeakHandoffAlong p).terminalMobius)

/--
PSL loop-equivariance data for canonical-terminal-sheet based weak handoff
continuation.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueEquivarianceDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (continuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData
        x₀ g localModels) where
  /-- PSL-valued real holonomy obtained from loop monodromy. -/
  holonomy : RealHolonomyRepresentation X x₀
  /-- Loop-precomposition of paths gives the PSL action on terminal values. -/
  terminal_path_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x),
      Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
      continuation.terminalValue (loop.trans p) =
        holonomy.upperHalfPlaneAction γ
          (continuation.terminalValue p)

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueEquivarianceDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData
        x₀ g localModels}

/--
Canonical-terminal-sheet based weak handoff continuation plus PSL loop
equivariance gives PSL path-class monodromy.
-/
noncomputable def toPathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueEquivarianceDataPSL
        C) :
    PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
      x₀ g localModels where
  pathClassContinuation :=
    C.toPathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData
      |>.toPathClassLocalTransitionAnalyticContinuationData
  holonomy := E.holonomy
  pathClass_equivariant := by
    intro γ x q
    induction q using Path.Homotopic.Quotient.ind with
    | mk p =>
        induction hloop : FundamentalGroup.toPath γ⁻¹ using
          Path.Homotopic.Quotient.ind with
        | mk loop =>
            rw [← Path.Homotopic.Quotient.mk_trans]
            change
              (C.toPathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData).terminalValueAt
                  x (Path.Homotopic.Quotient.mk (loop.trans p)) =
                E.holonomy.upperHalfPlaneAction γ
                  ((C.toPathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData).terminalValueAt
                    x (Path.Homotopic.Quotient.mk p))
            rw [
              PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData.terminalValueAt_mk,
              PathLocalTransitionBasedWeakHandoffTerminalBranchAnalyticContinuationValueData.terminalValueAt_mk]
            exact E.terminal_path_equivariant γ loop p hloop.symm

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueEquivarianceDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Terminal-center equality plus PSL terminal-Mobius covariance gives path-level
PSL loop equivariance of terminal values.
-/
noncomputable def ofTerminalProjectionEquivariance
    (holonomy : RealHolonomyRepresentation X x₀)
    (hCenter :
      ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
        {x : X} (p : Path x₀ x),
        Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
        (C.basedWeakHandoffAlong (loop.trans p)).terminalCenter =
          (C.basedWeakHandoffAlong p).terminalCenter)
    (hProjection :
      ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
        {x : X} (p : Path x₀ x),
        Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
        realMobiusProjection
            ((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) =
          holonomy γ *
            realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius)) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
      C where
  holonomy := holonomy
  terminal_path_equivariant := by
    intro γ loop x p hloop
    simpa [
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalValue]
      using
        (C.basedWeakHandoffAlong p).terminalValue_eq_holonomy_action_of_terminalProjection_eq
          (C.basedWeakHandoffAlong (loop.trans p)) holonomy γ
          (hCenter γ loop p hloop) (hProjection γ loop p hloop)

/--
Terminal-Mobius PSL covariance data imply path-level PSL value equivariance.
-/
noncomputable def ofTerminalProjectionEquivarianceData
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalProjectionEquivarianceDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
      C :=
  ofTerminalProjectionEquivariance E.holonomy
    E.terminalCenter_equivariant E.terminalProjection_equivariant

/--
Value-level PSL loop equivariance for the derived canonical-sheet value data
forgets to path-level PSL loop equivariance for agreement data.
-/
noncomputable def ofCanonicalSheetValueEquivarianceDataPSL
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueEquivarianceDataPSL
        C.toCanonicalSheetAnalyticContinuationValueData) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
      C where
  holonomy := E.holonomy
  terminal_path_equivariant := by
    intro γ loop x p hloop
    simpa [
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalValue,
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAnalyticContinuationValueData.terminalValue]
      using E.terminal_path_equivariant γ loop p hloop

/--
Terminal-sheet agreement plus PSL value equivariance gives the single-valued
canonical-cover PSL continuation record.
-/
noncomputable def toCanonicalCoverAnalyticContinuationDataPSL
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalCoverAnalyticContinuationDataPSL
      x₀ g localModels where
  basedWeakHandoffAlong := C.basedWeakHandoffAlong
  dev := C.dev
  holonomy := E.holonomy
  dev_eq_on_terminalSheet := by
    intro x p y' hy'
    exact C.dev_eq_on_terminalSheet p y' hy'
  dev_equivariant := by
    intro γ y
    exact
      C.dev_deckAction_eq_of_terminal_path_equivariant
        E.holonomy E.terminal_path_equivariant γ y

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Deck equivariance of the constructed upstairs map gives path-level PSL
loop equivariance of terminal values.

This is the reverse direction to
`dev_deckAction_eq_of_terminal_path_equivariant` at the level needed for
monodromy: loop-prepending moves the terminal cover point by the deck action,
and terminal-sheet agreement identifies terminal values with the upstairs map
at those terminal cover points.
-/
noncomputable def toValueEquivarianceDataPSL_of_dev_equivariant
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (holonomy : RealHolonomyRepresentation X x₀)
    (hdev :
      ∀ (γ : FundamentalGroup X x₀)
        (y : (canonicalContinuationCover x₀).total),
        C.dev ((canonicalContinuationCover x₀).deckAction γ y) =
          holonomy.upperHalfPlaneAction γ (C.dev y)) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
      C where
  holonomy := holonomy
  terminal_path_equivariant := by
    intro γ loop x p hloop
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong (loop.trans p)
    have hT :
        T.terminalCoverPoint =
          (canonicalContinuationCover x₀).deckAction γ S.terminalCoverPoint :=
      PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalCoverPoint_loopTrans_eq_deckAction
        γ loop S T hloop
    calc
      C.terminalValue (loop.trans p) =
          C.dev T.terminalCoverPoint := by
            simpa [PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalValue,
              T] using (C.dev_terminalCoverPoint (loop.trans p)).symm
      _ = C.dev ((canonicalContinuationCover x₀).deckAction γ S.terminalCoverPoint) := by
            rw [hT]
      _ = holonomy.upperHalfPlaneAction γ (C.dev S.terminalCoverPoint) := by
            exact hdev γ S.terminalCoverPoint
      _ = holonomy.upperHalfPlaneAction γ (C.terminalValue p) := by
            simpa [PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalValue,
              S] using
              congrArg (holonomy.upperHalfPlaneAction γ)
                (C.dev_terminalCoverPoint p)

/--
For canonical-terminal-sheet agreement data, deck equivariance of the
constructed upstairs map is equivalent to path-level PSL loop equivariance of
terminal values.
-/
theorem dev_deckAction_equivariant_iff_terminal_path_equivariant
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (holonomy : RealHolonomyRepresentation X x₀) :
    (∀ (γ : FundamentalGroup X x₀)
        (y : (canonicalContinuationCover x₀).total),
        C.dev ((canonicalContinuationCover x₀).deckAction γ y) =
          holonomy.upperHalfPlaneAction γ (C.dev y)) ↔
      (∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
        {x : X} (p : Path x₀ x),
        Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹ →
        C.terminalValue (loop.trans p) =
          holonomy.upperHalfPlaneAction γ (C.terminalValue p)) := by
  constructor
  · intro hdev γ loop x p hloop
    exact
      (C.toValueEquivarianceDataPSL_of_dev_equivariant holonomy hdev).terminal_path_equivariant
        γ loop p hloop
  · intro hpath γ y
    exact C.dev_deckAction_eq_of_terminal_path_equivariant
      holonomy hpath γ y

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

/--
Value-equivariance plus terminal-Mobius projection rigidity identifies the
derived loop-terminal PSL class with a genuine holonomy representation.

This is a smaller mathematical boundary than raw derived-holonomy data:
the monoid laws are inherited from the stored PSL representation, while the
remaining content is the identification of that representation with the
loop-terminal class and the rigidity step converting value equivariance into
transition-adjusted terminal-Mobius covariance.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- PSL value-equivariance for terminal-sheet agreement. -/
  valueEquivariance :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
      agreementContinuation
  /-- The value-equivariance holonomy is the loop-terminal derived PSL class. -/
  valueHolonomy_eq_derivedHolonomy :
    ∀ γ : FundamentalGroup X x₀,
      valueEquivariance.holonomy γ =
        agreementContinuation.derivedHolonomyProjection γ
  /--
  Rigidity of the local terminal formulas: value equivariance forces the
  transition-adjusted terminal-Mobius projection equality.
  -/
  automaticTerminalTransitionProjection_eq_of_valueEquivariance :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x)
      (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
      realMobiusProjection
          (((agreementContinuation.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            agreementContinuation.terminalTransitionRepresentative γ loop p hloop) =
        valueEquivariance.holonomy γ *
          realMobiusProjection
            ((agreementContinuation.basedWeakHandoffAlong p).terminalMobius)

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Value-projection data fill the derived-holonomy/cocycle record by inheriting
the identity and multiplication laws from the PSL representation.
-/
noncomputable def toAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
      C where
  derivedHolonomy_one := by
    rw [← D.valueHolonomy_eq_derivedHolonomy 1]
    exact RealHolonomyRepresentation.map_one D.valueEquivariance.holonomy
  derivedHolonomy_mul := by
    intro γ δ
    rw [← D.valueHolonomy_eq_derivedHolonomy (γ * δ),
      ← D.valueHolonomy_eq_derivedHolonomy γ,
      ← D.valueHolonomy_eq_derivedHolonomy δ]
    exact RealHolonomyRepresentation.map_mul D.valueEquivariance.holonomy γ δ
  automaticTerminalTransitionProjection_equivariant := by
    intro γ loop x p hloop
    rw [← D.valueHolonomy_eq_derivedHolonomy γ]
    exact
      D.automaticTerminalTransitionProjection_eq_of_valueEquivariance
        γ loop p hloop

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionDataPSL

/--
Value-equivariance plus terminal-Mobius projection rigidity.

This is sharper than
`PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionDataPSL`:
it does not separately assume that the value holonomy is the derived
loop-terminal holonomy.  That identification follows formally by applying the
projection-rigidity equality to the canonical representative loop and the base
normalization path.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- PSL value-equivariance for terminal-sheet agreement. -/
  valueEquivariance :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
      agreementContinuation
  /--
  Rigidity of the local terminal formulas: value equivariance forces the
  transition-adjusted terminal-Mobius projection equality.
  -/
  automaticTerminalTransitionProjection_eq_of_valueEquivariance :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x)
      (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
      realMobiusProjection
          (((agreementContinuation.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            agreementContinuation.terminalTransitionRepresentative γ loop p hloop) =
        valueEquivariance.holonomy γ *
          realMobiusProjection
            ((agreementContinuation.basedWeakHandoffAlong p).terminalMobius)

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
The holonomy appearing in value equivariance is forced to be the derived
loop-terminal PSL class.
-/
theorem valueHolonomy_eq_derivedHolonomy
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityDataPSL
        C)
    (γ : FundamentalGroup X x₀) :
    D.valueEquivariance.holonomy γ =
      C.derivedHolonomyProjection γ := by
  have hbase :=
    D.automaticTerminalTransitionProjection_eq_of_valueEquivariance
      γ (C.canonicalLoopFor γ) (x := x₀) C.baseNormalizationPath
      (C.canonicalLoopFor_spec γ)
  rw [PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.derivedHolonomyProjection,
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.loopAdjustedTerminalProjection,
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.baseTerminalProjection,
    hbase]
  simp [mul_assoc]

/--
Value-projection rigidity fills the older derived-holonomy value-projection
record; the holonomy-identification field is generated automatically.
-/
noncomputable def toDerivedHolonomyValueProjectionDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementDerivedHolonomyValueProjectionDataPSL
      C where
  valueEquivariance := D.valueEquivariance
  valueHolonomy_eq_derivedHolonomy := D.valueHolonomy_eq_derivedHolonomy
  automaticTerminalTransitionProjection_eq_of_valueEquivariance :=
    D.automaticTerminalTransitionProjection_eq_of_valueEquivariance

/--
Value-projection rigidity directly gives the derived-holonomy/cocycle record.
-/
noncomputable def toAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
      C :=
  D.toDerivedHolonomyValueProjectionDataPSL
    |>.toAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityDataPSL

/--
Terminal-formula PSL projection rigidity from deck equivariance of the
canonical-cover map.

This separates the last local analytic/contentful step from value
equivariance.  Once the upstairs developing map is deck-equivariant, the two
terminal local formulae representing the same sheet should determine the same
transition-adjusted PSL class.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /--
  Deck equivariance of the canonical-cover map forces the adjusted terminal
  Mobius class covariance.
  -/
  automaticTerminalTransitionProjection_eq_of_dev_equivariant :
    ∀ (holonomy : RealHolonomyRepresentation X x₀)
      (_hdev :
        ∀ (γ : FundamentalGroup X x₀)
          (y : (canonicalContinuationCover x₀).total),
          agreementContinuation.dev
              ((canonicalContinuationCover x₀).deckAction γ y) =
            holonomy.upperHalfPlaneAction γ
              (agreementContinuation.dev y))
      (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x)
      (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
      realMobiusProjection
          (((agreementContinuation.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            agreementContinuation.terminalTransitionRepresentative γ loop p hloop) =
        holonomy γ *
          realMobiusProjection
            ((agreementContinuation.basedWeakHandoffAlong p).terminalMobius)

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Terminal-formula projection rigidity plus value equivariance gives the
value-projection rigidity package.
-/
noncomputable def toValueProjectionRigidityDataPSL
    (R :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityDataPSL
        C)
    (E :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueProjectionRigidityDataPSL
      C where
  valueEquivariance := E
  automaticTerminalTransitionProjection_eq_of_valueEquivariance := by
    intro γ loop x p hloop
    exact
      R.automaticTerminalTransitionProjection_eq_of_dev_equivariant
        E.holonomy
        (fun δ y =>
          C.dev_deckAction_eq_of_terminal_path_equivariant
            E.holonomy E.terminal_path_equivariant δ y)
        γ loop p hloop

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityDataPSL

/--
PSL action faithfulness on the actual terminal coordinate agreement set.

This removes the continuation bookkeeping from the last local algebraic step:
after terminal formula agreement has been converted into equality of two PSL
actions on the coordinate agreement set, this field says that the set is large
enough to identify the PSL elements.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /--
  The selected coordinate agreement set is large enough to identify PSL
  transformations by their actions.
  -/
  terminalTransitionCoordinateAgreementSet_actionFaithful :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x)
      (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
      RealMobiusActionFaithfulOn
        (agreementContinuation.terminalTransitionCoordinateAgreementSet
          γ loop p hloop)

/--
Three-point richness of the actual terminal coordinate agreement set.

Together with the global fact that three points determine a PSL transformation,
this gives terminal-coordinate action faithfulness.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /--
  Every selected coordinate agreement set contains three pairwise distinct
  upper-half-plane points.
  -/
  terminalTransitionCoordinateAgreementSet_containsThreeDistinct :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x)
      (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
      ContainsThreeDistinctUpperHalfPlanePoints
        (agreementContinuation.terminalTransitionCoordinateAgreementSet
          γ loop p hloop)

/--
Nonempty-open-subset richness of the actual terminal coordinate agreement
set.

This is the topological boundary behind three-point richness: an open patch in
the upper half-plane contains infinitely many, hence at least three distinct,
coordinate points.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /--
  Every selected coordinate agreement set contains a nonempty open subset of
  the upper half-plane.
  -/
  terminalTransitionCoordinateAgreementSet_containsNonemptyOpen :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x)
      (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
      ∃ u : Set ℍ,
        IsOpen u ∧ u.Nonempty ∧
          u ⊆ agreementContinuation.terminalTransitionCoordinateAgreementSet
            γ loop p hloop

/--
Terminal-sheet agreement data automatically has nonempty-open terminal
coordinate agreement sets.
-/
def PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.toTerminalFormulaNonemptyOpenAgreementDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementDataPSL
      agreementContinuation where
  terminalTransitionCoordinateAgreementSet_containsNonemptyOpen :=
    fun γ loop _x p hloop =>
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalTransitionCoordinateAgreementSet_containsNonemptyOpen
        agreementContinuation γ loop p hloop

/--
Faithfulness of terminal local formulae at the PSL level.

This is the local analytic/algebraic endpoint of the projection-rigidity
story: if the transition-adjusted terminal formula agrees with the
holonomy-applied source terminal formula on the relevant common sheet
neighborhood, then the two PSL classes are equal.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /--
  Formula agreement on the common terminal-sheet/transition domain determines
  the transition-adjusted PSL projection.
  -/
  automaticTerminalTransitionProjection_eq_of_formula_agreement :
    ∀ (holonomy : RealHolonomyRepresentation X x₀)
      (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x)
      (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
      (∀ y : PathHomotopyUniversalCover X x₀,
        y ∈ (agreementContinuation.basedWeakHandoffAlong p).terminalSheet →
        (canonicalContinuationCover x₀).deckAction γ y ∈
          (agreementContinuation.basedWeakHandoffAlong (loop.trans p)).terminalSheet →
        PathHomotopyUniversalCover.endpoint y ∈
          (agreementContinuation.terminalTransitionData γ loop p hloop).neighborhood →
        agreementContinuation.terminalTransitionAdjustedFormulaAgreementAt
          holonomy γ loop p hloop y) →
      realMobiusProjection
          (((agreementContinuation.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            agreementContinuation.terminalTransitionRepresentative γ loop p hloop) =
        holonomy γ *
          realMobiusProjection
            ((agreementContinuation.basedWeakHandoffAlong p).terminalMobius)

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Terminal-formula faithfulness plus the formal deck-equivariant formula
comparison gives terminal-formula projection rigidity.
-/
noncomputable def toTerminalFormulaProjectionRigidityDataPSL
    (F :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityDataPSL
      C where
  automaticTerminalTransitionProjection_eq_of_dev_equivariant := by
    intro holonomy hdev γ loop x p hloop
    exact
      F.automaticTerminalTransitionProjection_eq_of_formula_agreement
        holonomy γ loop p hloop
        (fun y hySource hyTarget hyTransition =>
          C.terminalTransitionAdjustedFormula_eq_holonomy_action_of_dev_equivariant
            holonomy hdev γ loop p hloop y hySource hyTarget hyTransition)

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Nonempty open agreement sets give three-point richness.
-/
noncomputable def toTerminalFormulaThreePointRichnessDataPSL
    (O :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessDataPSL
      C where
  terminalTransitionCoordinateAgreementSet_containsThreeDistinct := by
    intro γ loop x p hloop
    rcases O.terminalTransitionCoordinateAgreementSet_containsNonemptyOpen
      γ loop p hloop with ⟨u, huOpen, huNonempty, huSubset⟩
    exact
      containsThreeDistinctUpperHalfPlanePoints_of_nonempty_open_subset
        huOpen huNonempty huSubset

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/-- Three-point richness gives terminal-coordinate action faithfulness. -/
noncomputable def toTerminalFormulaActionFaithfulnessDataPSL
    (T :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessDataPSL
      C where
  terminalTransitionCoordinateAgreementSet_actionFaithful := by
    intro γ loop x p hloop
    exact
      realMobiusActionFaithfulOn_of_containsThreeDistinctUpperHalfPlanePoints
        realMobiusActionDeterminedByThreePointsTheoremPSL
        (T.terminalTransitionCoordinateAgreementSet_containsThreeDistinct
          γ loop p hloop)

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Action faithfulness on the coordinate agreement set gives terminal-formula
projection faithfulness.
-/
noncomputable def toTerminalFormulaProjectionFaithfulnessDataPSL
    (F :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessDataPSL
      C where
  automaticTerminalTransitionProjection_eq_of_formula_agreement := by
    intro holonomy γ loop x p hloop hFormula
    exact
      F.terminalTransitionCoordinateAgreementSet_actionFaithful
        γ loop p hloop
        (realMobiusProjection
          (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            C.terminalTransitionRepresentative γ loop p hloop))
        (holonomy γ *
          realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius))
        (C.terminalTransitionActionAgreement_on_coordinateAgreementSet_of_formulaAgreement
          holonomy γ loop p hloop hFormula)

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

/--
Terminal-sheet agreement data automatically has three-point-rich terminal
coordinate agreement sets.
-/
noncomputable def toTerminalFormulaThreePointRichnessDataPSL
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaThreePointRichnessDataPSL
      C :=
  C.toTerminalFormulaNonemptyOpenAgreementDataPSL
    |>.toTerminalFormulaThreePointRichnessDataPSL

/--
Terminal-sheet agreement data automatically has PSL action faithfulness on the
terminal coordinate agreement sets.
-/
noncomputable def toTerminalFormulaActionFaithfulnessDataPSL
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaActionFaithfulnessDataPSL
      C :=
  C.toTerminalFormulaThreePointRichnessDataPSL
    |>.toTerminalFormulaActionFaithfulnessDataPSL

/--
Terminal-sheet agreement data automatically has PSL projection faithfulness for
the transition-adjusted terminal formulae.
-/
noncomputable def toTerminalFormulaProjectionFaithfulnessDataPSL
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessDataPSL
      C :=
  C.toTerminalFormulaActionFaithfulnessDataPSL
    |>.toTerminalFormulaProjectionFaithfulnessDataPSL

/--
Terminal-sheet agreement data automatically has terminal-formula PSL
projection rigidity.
-/
noncomputable def toTerminalFormulaProjectionRigidityDataPSL
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionRigidityDataPSL
      C :=
  C.toTerminalFormulaProjectionFaithfulnessDataPSL
    |>.toTerminalFormulaProjectionRigidityDataPSL

/--
Null-homotopic loop-prepending has trivial adjusted terminal PSL effect.

This is the identity-loop part of monodromy at arbitrary endpoints.  It uses
only terminal-sheet agreement: when `γ = 1`, the deck action is the identity,
so the source and loop-prepended terminal formulae compute the same upstairs
value on their common terminal-sheet patch.
-/
theorem automaticTerminalTransitionProjection_eq_of_identity_loop
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (loop : Path x₀ x₀) {x : X} (p : Path x₀ x)
    (hloop :
      Path.Homotopic.Quotient.mk loop =
        FundamentalGroup.toPath (1 : FundamentalGroup X x₀)⁻¹) :
    realMobiusProjection
        (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
          C.terminalTransitionRepresentative
            (1 : FundamentalGroup X x₀) loop p hloop) =
      realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius) := by
  classical
  let trivialHolonomy : RealHolonomyRepresentation X x₀ :=
    { toMonoidHom := 1 }
  have hProjection :
      realMobiusProjection
          (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            C.terminalTransitionRepresentative
              (1 : FundamentalGroup X x₀) loop p hloop) =
        trivialHolonomy (1 : FundamentalGroup X x₀) *
          realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius) := by
    refine
      C.toTerminalFormulaProjectionFaithfulnessDataPSL
        |>.automaticTerminalTransitionProjection_eq_of_formula_agreement
          trivialHolonomy (1 : FundamentalGroup X x₀) loop p hloop ?_
    intro y hySource hyTarget hyTransition
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong (loop.trans p)
    let A :=
      C.terminalTransitionRepresentative
        (1 : FundamentalGroup X x₀) loop p hloop
    have hDeck :
        (canonicalContinuationCover x₀).deckAction
            (1 : FundamentalGroup X x₀) y = y := by
      simp [canonicalContinuationCover]
    have hEndpoint :
        PathHomotopyUniversalCover.endpoint
            ((canonicalContinuationCover x₀).deckAction
              (1 : FundamentalGroup X x₀) y) =
          PathHomotopyUniversalCover.endpoint y := by
      rw [hDeck]
    have hTargetFormula :=
      C.dev_eq_on_terminalSheet (loop.trans p)
        ((canonicalContinuationCover x₀).deckAction
          (1 : FundamentalGroup X x₀) y) hyTarget
    have hSourceFormula :=
      C.dev_eq_on_terminalSheet p y hySource
    have hTransition :
        (localModels.chartAt T.terminalCenter).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y) =
          realMobiusRepresentativeAction A
            ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
              (PathHomotopyUniversalCover.endpoint y)) := by
      simpa [S, T, A,
        PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalTransitionRepresentative]
        using
          (C.terminalTransitionData
              (1 : FundamentalGroup X x₀) loop p hloop).transition_eq
            (PathHomotopyUniversalCover.endpoint y) hyTransition
    calc
      realMobiusRepresentativeAction
          (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            C.terminalTransitionRepresentative
              (1 : FundamentalGroup X x₀) loop p hloop)
          ((localModels.chartAt
              ((C.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y))
          =
        realMobiusRepresentativeAction T.terminalMobius
          (realMobiusRepresentativeAction A
            ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
              (PathHomotopyUniversalCover.endpoint y))) := by
            simp [S, T, A, realMobiusRepresentativeAction_mul]
      _ =
        realMobiusRepresentativeAction T.terminalMobius
          ((localModels.chartAt T.terminalCenter).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y)) := by
            rw [← hTransition]
      _ =
        realMobiusRepresentativeAction T.terminalMobius
          ((localModels.chartAt T.terminalCenter).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint
              ((canonicalContinuationCover x₀).deckAction
                (1 : FundamentalGroup X x₀) y))) := by
            rw [hEndpoint]
      _ =
        C.dev ((canonicalContinuationCover x₀).deckAction
          (1 : FundamentalGroup X x₀) y) := by
            simpa [T] using hTargetFormula.symm
      _ = C.dev y := by
            rw [hDeck]
      _ =
        realMobiusRepresentativeAction
          ((C.basedWeakHandoffAlong p).terminalMobius)
          ((localModels.chartAt
              ((C.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
            (PathHomotopyUniversalCover.endpoint y)) := by
            rw [hSourceFormula]
      _ =
        trivialHolonomy.upperHalfPlaneAction
          (1 : FundamentalGroup X x₀)
          (realMobiusRepresentativeAction
            ((C.basedWeakHandoffAlong p).terminalMobius)
            ((localModels.chartAt
                ((C.basedWeakHandoffAlong p).terminalCenter)).toUpperHalfPlane
              (PathHomotopyUniversalCover.endpoint y))) := by
            simp [trivialHolonomy]
  simpa [trivialHolonomy] using hProjection

/--
The derived loop-terminal PSL assignment sends the identity deck
transformation to the identity.

This is the first genuine monodromy/cocycle field.  No global equivariant
developing map is assumed: for the identity deck transformation, the source
and target terminal-sheet formulae both compute the same constructed upstairs
value on the common sheet, and terminal-formula faithfulness identifies the
adjusted terminal PSL class with the base terminal class.
-/
theorem derivedHolonomyProjection_one
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) :
    C.derivedHolonomyProjection (1 : FundamentalGroup X x₀) = 1 := by
  let loop := C.canonicalLoopFor (1 : FundamentalGroup X x₀)
  let p := C.baseNormalizationPath
  have hProjection :
      realMobiusProjection
          (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            C.terminalTransitionRepresentative
              (1 : FundamentalGroup X x₀) loop p
              (by simpa [loop] using
                (C.canonicalLoopFor_spec (1 : FundamentalGroup X x₀)))) =
        realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius) :=
    C.automaticTerminalTransitionProjection_eq_of_identity_loop loop p
      (by simpa [loop] using
        (C.canonicalLoopFor_spec (1 : FundamentalGroup X x₀)))
  rw [derivedHolonomyProjection, loopAdjustedTerminalProjection,
    baseTerminalProjection]
  simpa [loop, p, mul_assoc] using
    congrArg (fun A : RealMobiusGroup =>
      A * (realMobiusProjection
        ((C.basedWeakHandoffAlong C.baseNormalizationPath).terminalMobius))⁻¹)
      hProjection

/--
Arbitrary loop-prepending covariance forces multiplication of the derived
loop-terminal PSL assignment.

The proof compares the direct continuation for `γ * δ` with the two-step
continuation through `δ` and then `γ`.  The terminal-chart cocycle identifies
the two-step chart change, while endpoint-fixed homotopy invariance removes
the harmless choices of parenthesization and canonical loop representative.
-/
theorem derivedHolonomyProjection_mul_of_automaticTerminalTransitionProjection_equivariant
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (hEquiv :
      ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
        {x : X} (p : Path x₀ x)
        (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
        realMobiusProjection
            (((C.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
              C.terminalTransitionRepresentative γ loop p hloop) =
          C.derivedHolonomyProjection γ *
            realMobiusProjection ((C.basedWeakHandoffAlong p).terminalMobius))
    (γ δ : FundamentalGroup X x₀) :
    C.derivedHolonomyProjection (γ * δ) =
      C.derivedHolonomyProjection γ * C.derivedHolonomyProjection δ := by
  classical
  let p₀ := C.baseNormalizationPath
  let loopγ := C.canonicalLoopFor γ
  let loopδ := C.canonicalLoopFor δ
  let pδ : Path x₀ x₀ := loopδ.trans p₀
  let pStep : Path x₀ x₀ := loopγ.trans pδ
  let pDirect : Path x₀ x₀ := (loopγ.trans loopδ).trans p₀
  let pCanonical : Path x₀ x₀ := (C.canonicalLoopFor (γ * δ)).trans p₀
  let M₀ := (C.basedWeakHandoffAlong p₀).terminalMobius
  let Mδ := (C.basedWeakHandoffAlong pδ).terminalMobius
  let MStep := (C.basedWeakHandoffAlong pStep).terminalMobius
  let MDirect := (C.basedWeakHandoffAlong pDirect).terminalMobius
  let MCanonical := (C.basedWeakHandoffAlong pCanonical).terminalMobius
  have hBetween :=
    C.terminalTransitionRepresentativeBetween_loopTrans_projection_eq_of_automaticTerminalTransitionProjection_equivariant
      (fun η => C.derivedHolonomyProjection η) hEquiv
  have hδ :
      realMobiusProjection
          (Mδ * C.terminalTransitionRepresentativeBetween p₀ pδ) =
        C.derivedHolonomyProjection δ * realMobiusProjection M₀ := by
    simpa [p₀, loopδ, pδ, Mδ, M₀] using
      hBetween δ loopδ p₀ (C.canonicalLoopFor_spec δ)
  have hγStep :
      realMobiusProjection
          (MStep * C.terminalTransitionRepresentativeBetween pδ pStep) =
        C.derivedHolonomyProjection γ * realMobiusProjection Mδ := by
    simpa [loopγ, pδ, pStep, MStep, Mδ] using
      hBetween γ loopγ pδ (C.canonicalLoopFor_spec γ)
  have hStepVia :
      realMobiusProjection
          (MStep * C.terminalTransitionRepresentativeBetween p₀ pStep) =
        (C.derivedHolonomyProjection γ *
            C.derivedHolonomyProjection δ) *
          realMobiusProjection M₀ := by
    calc
      realMobiusProjection
          (MStep * C.terminalTransitionRepresentativeBetween p₀ pStep)
          =
        realMobiusProjection
          ((MStep * C.terminalTransitionRepresentativeBetween pδ pStep) *
            C.terminalTransitionRepresentativeBetween p₀ pδ) := by
          exact
            C.terminalTransitionRepresentativeBetween_adjusted_projection_trans
              p₀ pδ pStep MStep
      _ =
        realMobiusProjection
            (MStep * C.terminalTransitionRepresentativeBetween pδ pStep) *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween p₀ pδ) := by
          simp
      _ =
        (C.derivedHolonomyProjection γ * realMobiusProjection Mδ) *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween p₀ pδ) := by
          rw [hγStep]
      _ =
        C.derivedHolonomyProjection γ *
          realMobiusProjection
            (Mδ * C.terminalTransitionRepresentativeBetween p₀ pδ) := by
          simp [mul_assoc]
      _ =
        C.derivedHolonomyProjection γ *
          (C.derivedHolonomyProjection δ * realMobiusProjection M₀) := by
          rw [hδ]
      _ =
        (C.derivedHolonomyProjection γ *
            C.derivedHolonomyProjection δ) *
          realMobiusProjection M₀ := by
          simp [mul_assoc]
  have hDirectStep : Path.Homotopic pDirect pStep := by
    simpa [pDirect, pStep, pδ, p₀] using
      Path.Homotopic.trans_assoc loopγ loopδ p₀
  have hDirectFromStep :
      realMobiusProjection
          (MDirect * C.terminalTransitionRepresentativeBetween p₀ pDirect) =
          realMobiusProjection
          (MStep * C.terminalTransitionRepresentativeBetween p₀ pStep) := by
    have hHom :
        realMobiusProjection
            (MStep * C.terminalTransitionRepresentativeBetween pDirect pStep) =
          realMobiusProjection MDirect := by
      simpa [pDirect, pStep, MStep, MDirect] using
        C.terminalTransitionRepresentativeBetween_adjusted_projection_eq_of_homotopic
          pDirect pStep hDirectStep
    exact
      (calc
        realMobiusProjection
            (MStep * C.terminalTransitionRepresentativeBetween p₀ pStep)
            =
          realMobiusProjection
            ((MStep * C.terminalTransitionRepresentativeBetween pDirect pStep) *
              C.terminalTransitionRepresentativeBetween p₀ pDirect) := by
            exact
              C.terminalTransitionRepresentativeBetween_adjusted_projection_trans
                p₀ pDirect pStep MStep
        _ =
          realMobiusProjection
              (MStep * C.terminalTransitionRepresentativeBetween pDirect pStep) *
            realMobiusProjection
              (C.terminalTransitionRepresentativeBetween p₀ pDirect) := by
            simp
        _ =
          realMobiusProjection MDirect *
            realMobiusProjection
              (C.terminalTransitionRepresentativeBetween p₀ pDirect) := by
            rw [hHom]
        _ =
          realMobiusProjection
            (MDirect * C.terminalTransitionRepresentativeBetween p₀ pDirect) := by
            simp).symm
  have hLoopProduct :
      Path.Homotopic.Quotient.mk (loopγ.trans loopδ) =
        FundamentalGroup.toPath (γ * δ)⁻¹ := by
    change
      Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk loopγ)
          (Path.Homotopic.Quotient.mk loopδ) =
        FundamentalGroup.toPath (γ * δ)⁻¹
    rw [C.canonicalLoopFor_spec γ, C.canonicalLoopFor_spec δ]
    rw [mul_inv_rev]
    rfl
  have hDirectCanonical : Path.Homotopic pDirect pCanonical := by
    have hMk :
        Path.Homotopic.Quotient.mk pDirect =
          Path.Homotopic.Quotient.mk pCanonical := by
      change
        Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.mk (loopγ.trans loopδ))
            (Path.Homotopic.Quotient.mk p₀) =
          Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.mk (C.canonicalLoopFor (γ * δ)))
            (Path.Homotopic.Quotient.mk p₀)
      rw [hLoopProduct, C.canonicalLoopFor_spec (γ * δ)]
    exact Path.Homotopic.Quotient.eq.mp hMk
  have hCanonicalFromDirect :
      realMobiusProjection
          (MCanonical * C.terminalTransitionRepresentativeBetween p₀ pCanonical) =
        realMobiusProjection
          (MDirect * C.terminalTransitionRepresentativeBetween p₀ pDirect) := by
    have hHom :
        realMobiusProjection
            (MCanonical * C.terminalTransitionRepresentativeBetween pDirect pCanonical) =
          realMobiusProjection MDirect := by
      simpa [pDirect, pCanonical, MCanonical, MDirect] using
        C.terminalTransitionRepresentativeBetween_adjusted_projection_eq_of_homotopic
          pDirect pCanonical hDirectCanonical
    calc
      realMobiusProjection
          (MCanonical * C.terminalTransitionRepresentativeBetween p₀ pCanonical)
          =
        realMobiusProjection
          ((MCanonical * C.terminalTransitionRepresentativeBetween pDirect pCanonical) *
            C.terminalTransitionRepresentativeBetween p₀ pDirect) := by
          exact
            C.terminalTransitionRepresentativeBetween_adjusted_projection_trans
              p₀ pDirect pCanonical MCanonical
      _ =
        realMobiusProjection
            (MCanonical * C.terminalTransitionRepresentativeBetween pDirect pCanonical) *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween p₀ pDirect) := by
          simp
      _ =
        realMobiusProjection MDirect *
          realMobiusProjection
            (C.terminalTransitionRepresentativeBetween p₀ pDirect) := by
          rw [hHom]
      _ =
        realMobiusProjection
          (MDirect * C.terminalTransitionRepresentativeBetween p₀ pDirect) := by
          simp
  have hCanonicalOldBetween :
      C.loopAdjustedTerminalProjection (γ * δ) =
        realMobiusProjection
          (MCanonical * C.terminalTransitionRepresentativeBetween p₀ pCanonical) := by
    have hBetweenCanonical :=
      C.terminalTransitionRepresentative_projection_eq_between
        (γ * δ) (C.canonicalLoopFor (γ * δ)) p₀
        (C.canonicalLoopFor_spec (γ * δ))
    rw [loopAdjustedTerminalProjection]
    calc
      realMobiusProjection
          (((C.basedWeakHandoffAlong
              ((C.canonicalLoopFor (γ * δ)).trans C.baseNormalizationPath)).terminalMobius) *
            C.terminalTransitionRepresentative (γ * δ)
              (C.canonicalLoopFor (γ * δ)) (x := x₀)
              C.baseNormalizationPath (C.canonicalLoopFor_spec (γ * δ)))
          =
        realMobiusProjection
          (MCanonical *
            C.terminalTransitionRepresentative (γ * δ)
              (C.canonicalLoopFor (γ * δ)) (x := x₀)
              p₀ (C.canonicalLoopFor_spec (γ * δ))) := by
          simp [MCanonical, pCanonical, p₀]
      _ =
        realMobiusProjection
          (MCanonical *
            C.terminalTransitionRepresentativeBetween p₀ pCanonical) := by
          calc
            realMobiusProjection
              (MCanonical *
                C.terminalTransitionRepresentative (γ * δ)
                  (C.canonicalLoopFor (γ * δ)) (x := x₀)
                  p₀ (C.canonicalLoopFor_spec (γ * δ)))
                =
              realMobiusProjection MCanonical *
                realMobiusProjection
                  (C.terminalTransitionRepresentative (γ * δ)
                    (C.canonicalLoopFor (γ * δ)) (x := x₀)
                    p₀ (C.canonicalLoopFor_spec (γ * δ))) := by
                simp
            _ =
              realMobiusProjection MCanonical *
                realMobiusProjection
                  (C.terminalTransitionRepresentativeBetween p₀ pCanonical) := by
                rw [hBetweenCanonical]
            _ =
              realMobiusProjection
                (MCanonical *
                  C.terminalTransitionRepresentativeBetween p₀ pCanonical) := by
                simp
  have hMulWithBase :
      C.derivedHolonomyProjection (γ * δ) *
          realMobiusProjection M₀ =
        (C.derivedHolonomyProjection γ *
            C.derivedHolonomyProjection δ) *
          realMobiusProjection M₀ := by
    calc
      C.derivedHolonomyProjection (γ * δ) * realMobiusProjection M₀
          = C.loopAdjustedTerminalProjection (γ * δ) := by
            rw [C.loopAdjustedTerminalProjection_eq_derivedHolonomyProjection_mul_base]
            simp [baseTerminalProjection, M₀, p₀]
      _ =
        realMobiusProjection
          (MCanonical * C.terminalTransitionRepresentativeBetween p₀ pCanonical) := by
          rw [hCanonicalOldBetween]
      _ =
        realMobiusProjection
          (MDirect * C.terminalTransitionRepresentativeBetween p₀ pDirect) := by
          rw [hCanonicalFromDirect]
      _ =
        realMobiusProjection
          (MStep * C.terminalTransitionRepresentativeBetween p₀ pStep) := by
          rw [hDirectFromStep]
      _ =
        (C.derivedHolonomyProjection γ *
            C.derivedHolonomyProjection δ) *
          realMobiusProjection M₀ := hStepVia
  have hCancel :=
    congrArg (fun A : RealMobiusGroup => A * (realMobiusProjection M₀)⁻¹)
      hMulWithBase
  simpa [mul_assoc] using hCancel

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

/--
Reduced derived-holonomy monodromy data for canonical-sheet agreement.

The identity law is no longer a hypothesis: it is forced by terminal-sheet
agreement and terminal-formula faithfulness, via
`PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.derivedHolonomyProjection_one`.
The multiplication law is also forced by arbitrary loop-prepending covariance,
using terminal-chart cocycles and endpoint-fixed homotopy invariance.  The
remaining mathematical content is therefore exactly that arbitrary covariance
field.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /--
  Loop-precomposition multiplies arbitrary adjusted terminal Mobius classes by
  the derived loop-terminal holonomy.
  -/
  automaticTerminalTransitionProjection_equivariant :
    ∀ (γ : FundamentalGroup X x₀) (loop : Path x₀ x₀)
      {x : X} (p : Path x₀ x)
      (hloop : Path.Homotopic.Quotient.mk loop = FundamentalGroup.toPath γ⁻¹),
      realMobiusProjection
          (((agreementContinuation.basedWeakHandoffAlong (loop.trans p)).terminalMobius) *
            agreementContinuation.terminalTransitionRepresentative γ loop p hloop) =
        agreementContinuation.derivedHolonomyProjection γ *
          realMobiusProjection
            ((agreementContinuation.basedWeakHandoffAlong p).terminalMobius)

/--
Canonical-loop covariance data for the derived PSL holonomy.

This is smaller than `PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyDataPSL`:
it only asks for covariance for the canonical loop representative selected by
`Quot.out`.  Arbitrary loop representatives are recovered by endpoint-fixed
homotopy invariance of the transition-adjusted terminal class.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /--
  Continuing along the canonical representative loop for `γ` multiplies every
  adjusted terminal Mobius class by the derived loop-terminal holonomy.
  -/
  canonicalLoopTransitionProjection_equivariant :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x),
      realMobiusProjection
          (((agreementContinuation.basedWeakHandoffAlong
              ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalMobius) *
            agreementContinuation.terminalTransitionRepresentativeBetween p
              ((agreementContinuation.canonicalLoopFor γ).trans p)) =
        agreementContinuation.derivedHolonomyProjection γ *
          realMobiusProjection
            ((agreementContinuation.basedWeakHandoffAlong p).terminalMobius)

/--
Normalized canonical-loop terminal projection propagation.

This is the most local form of the remaining PSL monodromy boundary: the
loop-terminal class, normalized by the terminal class of the endpoint path, is
constant as the endpoint path varies.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /--
  The normalized canonical-loop terminal projection is transported unchanged
  from the base normalization path to every based path.
  -/
  canonicalLoopNormalizedProjection_propagates_from_base :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x),
      agreementContinuation.canonicalLoopNormalizedTerminalProjection γ p =
        agreementContinuation.canonicalLoopNormalizedTerminalProjection γ
          agreementContinuation.baseNormalizationPath

/--
Canonical-cover constancy of the normalized canonical-loop terminal
projection.

This is the geometric form of the remaining PSL monodromy boundary: after the
terminal class is normalized away, the canonical-loop terminal class descends to
a locally continued object on the canonical path-homotopy cover and is constant
there.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /--
  The normalized canonical-loop terminal projection is constant on the
  canonical path-homotopy cover, with value fixed at the base lift.
  -/
  canonicalLoopNormalizedProjectionAt_eq_base :
    ∀ (γ : FundamentalGroup X x₀)
      (y : PathHomotopyUniversalCover X x₀),
      agreementContinuation.canonicalLoopNormalizedProjectionAt γ y =
        agreementContinuation.canonicalLoopNormalizedProjectionAt γ
          (PathHomotopyUniversalCover.baseLift x₀)

/--
Local constancy on the canonical cover of the normalized canonical-loop
terminal projection.

Because the canonical path-homotopy cover is preconnected, this local form is
enough to recover the global constancy package.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /--
  For every loop class, the normalized canonical-loop projection is locally
  constant on the canonical path-homotopy cover.
  -/
  canonicalLoopNormalizedProjectionAt_locallyConstant :
    ∀ (γ : FundamentalGroup X x₀),
      IsLocallyConstant
        (agreementContinuation.canonicalLoopNormalizedProjectionAt γ)

/--
Local sheet constancy of the normalized canonical-loop projection.

For a path `p`, compare its terminal sheet with the terminal sheet obtained
after prepending the canonical loop for `γ`.  On the neighborhood where a cover
point lies in the first sheet and its `γ`-deck translate lies in the second,
the normalized canonical-loop class is unchanged.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalSheetConstancyDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /--
  The normalized canonical-loop terminal projection is constant on the
  deck-compatible pair of terminal sheets attached to `p` and to
  `(canonicalLoopFor γ).trans p`.
  -/
  canonicalLoopNormalizedProjectionAt_eq_on_deck_terminalSheets :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x)
      (y : PathHomotopyUniversalCover X x₀),
      y ∈ (agreementContinuation.basedWeakHandoffAlong p).terminalSheet →
      (canonicalContinuationCover x₀).deckAction γ y ∈
        (agreementContinuation.basedWeakHandoffAlong
          ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheet →
      agreementContinuation.canonicalLoopNormalizedProjectionAt γ y =
        agreementContinuation.canonicalLoopNormalizedProjectionAt γ
          (agreementContinuation.basedWeakHandoffAlong p).terminalCoverPoint

/--
Pure terminal-transition transport for the normalized canonical-loop
projection.

This is the remaining transition-class assertion after terminal-sheet
extension agreement has been split off: the PSL class of the terminal chart
transition between `p` and `(canonicalLoopFor γ).trans p` is unchanged after
the deck-compatible terminal-sheet extensions.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionTransportDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /--
  The terminal transition class between the source and loop-prepended terminal
  charts is transported unchanged along deck-compatible terminal-sheet
  extensions.
  -/
  terminalTransitionRepresentativeBetween_terminalSheetExtension_projection_eq :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x)
      (y : PathHomotopyUniversalCover X x₀)
      (hy : y ∈ (agreementContinuation.basedWeakHandoffAlong p).terminalSheet)
      (hdeck :
        PathHomotopyUniversalCover.deckAction γ y ∈
          (agreementContinuation.basedWeakHandoffAlong
            ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheet),
      realMobiusProjection
          (agreementContinuation.terminalTransitionRepresentativeBetween
            (p.trans
              ((agreementContinuation.basedWeakHandoffAlong p).terminalSheetPathInSet hy))
            (((agreementContinuation.canonicalLoopFor γ).trans p).trans
              ((agreementContinuation.basedWeakHandoffAlong
                ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheetPathInSet
                  (y' := PathHomotopyUniversalCover.deckAction γ y) hdeck))) =
        realMobiusProjection
          (agreementContinuation.terminalTransitionRepresentativeBetween p
            ((agreementContinuation.canonicalLoopFor γ).trans p))

/--
Terminal-sheet transport data for the normalized canonical-loop projection.

This is the geometric transition-transport form of the local-sheet monodromy
boundary.  It separates two pieces:

* extending a selected path inside its terminal sheet does not change the
  terminal chart/Mobius branch; and
* the PSL class of the terminal chart transition between `p` and
  `(canonicalLoopFor γ).trans p` is unchanged after making the compatible
  terminal-sheet extensions on both sides.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- Coherent terminal-sheet extension keeps terminal branch data unchanged. -/
  terminalSheetExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
      x₀ g localModels agreementContinuation.basedWeakHandoffAlong
  /--
  The terminal transition class between the source and loop-prepended terminal
  charts is transported unchanged along deck-compatible terminal-sheet
  extensions.
  -/
  terminalTransitionRepresentativeBetween_terminalSheetExtension_projection_eq :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x)
      (y : PathHomotopyUniversalCover X x₀)
      (hy : y ∈ (agreementContinuation.basedWeakHandoffAlong p).terminalSheet)
      (hdeck :
        PathHomotopyUniversalCover.deckAction γ y ∈
          (agreementContinuation.basedWeakHandoffAlong
            ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheet),
      realMobiusProjection
          (agreementContinuation.terminalTransitionRepresentativeBetween
            (p.trans
              ((agreementContinuation.basedWeakHandoffAlong p).terminalSheetPathInSet hy))
            (((agreementContinuation.canonicalLoopFor γ).trans p).trans
              ((agreementContinuation.basedWeakHandoffAlong
                ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheetPathInSet
                  (y' := PathHomotopyUniversalCover.deckAction γ y) hdeck))) =
      realMobiusProjection
          (agreementContinuation.terminalTransitionRepresentativeBetween p
            ((agreementContinuation.canonicalLoopFor γ).trans p))

/--
Preconnected-overlap data for terminal-transition transport.

This is a more geometric form of the remaining terminal-transition monodromy
boundary.  After terminal-sheet extension agreement fixes the terminal charts,
it asks only that the original endpoint and the deck-compatible terminal-sheet
endpoint lie in one preconnected piece of the overlap of those two fixed
terminal charts.  The PSL transition class is then forced to be constant on
that piece.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionPreconnectedOverlapDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- Coherent terminal-sheet extension keeps terminal branch data unchanged. -/
  terminalSheetExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
      x₀ g localModels agreementContinuation.basedWeakHandoffAlong
  /--
  The original terminal endpoint and a deck-compatible terminal-sheet endpoint
  can be compared inside one preconnected overlap of the fixed source and
  loop-prepended terminal charts.
  -/
  terminalTransitionPreconnectedOverlap :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x)
      (y : PathHomotopyUniversalCover X x₀)
      (_hy : y ∈ (agreementContinuation.basedWeakHandoffAlong p).terminalSheet)
      (_hdeck :
        PathHomotopyUniversalCover.deckAction γ y ∈
          (agreementContinuation.basedWeakHandoffAlong
            ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheet),
      ∃ W : Set X,
        IsPreconnected W ∧
        x ∈ W ∧
        PathHomotopyUniversalCover.endpoint y ∈ W ∧
        W ⊆
          (localModels.chartAt
              ((agreementContinuation.basedWeakHandoffAlong p).terminalCenter)).domain ∩
            (localModels.chartAt
              ((agreementContinuation.basedWeakHandoffAlong
                ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalCenter)).domain

/--
Same-overlap-component data for terminal-transition transport.

This is the sharp topological form of the terminal-transition boundary:
after terminal-sheet extension agreement fixes the terminal charts, the
deck-compatible endpoint must lie in the same connected component of the
overlap of those fixed terminal charts as the original endpoint.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionSameOverlapComponentDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- Coherent terminal-sheet extension keeps terminal branch data unchanged. -/
  terminalSheetExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
      x₀ g localModels agreementContinuation.basedWeakHandoffAlong
  /--
  The deck-compatible endpoint stays in the connected component of the fixed
  source/loop-prepended terminal-chart overlap containing the original
  endpoint.
  -/
  terminalTransitionEndpoint_mem_sameOverlapComponent :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x)
      (y : PathHomotopyUniversalCover X x₀)
      (_hy : y ∈ (agreementContinuation.basedWeakHandoffAlong p).terminalSheet)
      (_hdeck :
        PathHomotopyUniversalCover.deckAction γ y ∈
          (agreementContinuation.basedWeakHandoffAlong
            ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheet),
      PathHomotopyUniversalCover.endpoint y ∈
        connectedComponentIn
          ((localModels.chartAt
              ((agreementContinuation.basedWeakHandoffAlong p).terminalCenter)).domain ∩
            (localModels.chartAt
              ((agreementContinuation.basedWeakHandoffAlong
                ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalCenter)).domain)
          x

/--
Terminal-sheet path overlap data for terminal-transition transport.

This is a path-level sufficient condition for the same-overlap-component
boundary: the canonical path inside the source terminal sheet from the
original endpoint to the transported endpoint stays inside the target
terminal chart as well.  Since it already stays inside the source terminal
chart, its image is a path in the fixed terminal-chart overlap.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapPathDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- Coherent terminal-sheet extension keeps terminal branch data unchanged. -/
  terminalSheetExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
      x₀ g localModels agreementContinuation.basedWeakHandoffAlong
  /--
  The source terminal-sheet path from the original endpoint to the transported
  endpoint stays in the loop-prepended terminal chart.
  -/
  terminalSheetPath_mem_targetTerminalDomain :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x)
      (y : PathHomotopyUniversalCover X x₀)
      (hy : y ∈ (agreementContinuation.basedWeakHandoffAlong p).terminalSheet)
      (_hdeck :
        PathHomotopyUniversalCover.deckAction γ y ∈
          (agreementContinuation.basedWeakHandoffAlong
            ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheet)
      (t : unitInterval),
      (agreementContinuation.basedWeakHandoffAlong p).terminalSheetPathInSet hy t ∈
        (localModels.chartAt
          ((agreementContinuation.basedWeakHandoffAlong
            ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalCenter)).domain

/--
Existence of an overlap path for terminal-transition transport.

This is the intrinsic path-component form of the topological boundary: for the
fixed source and loop-prepended terminal charts, there is some path in their
overlap from the original endpoint to the transported endpoint.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapConnectingPathDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- Coherent terminal-sheet extension keeps terminal branch data unchanged. -/
  terminalSheetExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
      x₀ g localModels agreementContinuation.basedWeakHandoffAlong
  /--
  There is a path in the fixed terminal-chart overlap from the original
  endpoint to the transported endpoint.
  -/
  terminalTransitionOverlapConnectingPath :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x)
      (y : PathHomotopyUniversalCover X x₀)
      (_hy : y ∈ (agreementContinuation.basedWeakHandoffAlong p).terminalSheet)
      (_hdeck :
        PathHomotopyUniversalCover.deckAction γ y ∈
          (agreementContinuation.basedWeakHandoffAlong
            ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheet),
      ∃ ρ : Path x (PathHomotopyUniversalCover.endpoint y),
        ∀ t : unitInterval,
          ρ t ∈
            (localModels.chartAt
                ((agreementContinuation.basedWeakHandoffAlong p).terminalCenter)).domain ∩
              (localModels.chartAt
                ((agreementContinuation.basedWeakHandoffAlong
                  ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalCenter)).domain

/--
Upstairs overlap-path data for terminal-transition transport.

This is the cover-geometric version of the connecting-path boundary: from the
source terminal cover point to `y`, there is a path that stays in the source
terminal sheet and whose deck translate stays in the loop-prepended terminal
sheet.  Projecting this path gives a path in the fixed terminal-chart overlap.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverOverlapPathDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- Coherent terminal-sheet extension keeps terminal branch data unchanged. -/
  terminalSheetExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
      x₀ g localModels agreementContinuation.basedWeakHandoffAlong
  /--
  There is an upstairs path from the source terminal cover point to `y` whose
  projection stays in the fixed terminal-chart overlap.
  -/
  terminalTransitionCoverOverlapPath :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x)
      (y : PathHomotopyUniversalCover X x₀)
      (_hy : y ∈ (agreementContinuation.basedWeakHandoffAlong p).terminalSheet)
      (_hdeck :
        PathHomotopyUniversalCover.deckAction γ y ∈
          (agreementContinuation.basedWeakHandoffAlong
            ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheet),
      ∃ κ : Path (agreementContinuation.basedWeakHandoffAlong p).terminalCoverPoint y,
        ∀ t : unitInterval,
          κ t ∈ (agreementContinuation.basedWeakHandoffAlong p).terminalSheet ∧
            PathHomotopyUniversalCover.deckAction γ (κ t) ∈
              (agreementContinuation.basedWeakHandoffAlong
                ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheet

/--
Upstairs same-component data for terminal-transition transport.

This is the intrinsic cover-geometric monodromy boundary: inside the source
terminal sheet and the deck-preimage of the loop-prepended terminal sheet,
`y` must lie in the same connected component as the source terminal cover
point.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverSameComponentDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- Coherent terminal-sheet extension keeps terminal branch data unchanged. -/
  terminalSheetExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
      x₀ g localModels agreementContinuation.basedWeakHandoffAlong
  /--
  `y` is in the connected component of the deck-compatible overlap containing
  the source terminal cover point.
  -/
  terminalTransitionEndpoint_mem_sameCoverComponent :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x)
      (y : PathHomotopyUniversalCover X x₀)
      (_hy : y ∈ (agreementContinuation.basedWeakHandoffAlong p).terminalSheet)
      (_hdeck :
        PathHomotopyUniversalCover.deckAction γ y ∈
          (agreementContinuation.basedWeakHandoffAlong
            ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheet),
      let S := agreementContinuation.basedWeakHandoffAlong p
      let T :=
        agreementContinuation.basedWeakHandoffAlong
          ((agreementContinuation.canonicalLoopFor γ).trans p)
      y ∈
        connectedComponentIn
          (S.terminalSheet ∩
            (PathHomotopyUniversalCover.deckAction γ) ⁻¹' T.terminalSheet)
          S.terminalCoverPoint

/--
Downstairs same-component data for terminal-transition transport.

This asks only that the terminal endpoint lie in the same connected component
of the base overlap of the two terminal sheet charts. The corresponding
upstairs cover-same-component statement follows from local constancy of sheet
labels on connected components of a base overlap.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionBaseSameComponentDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- Coherent terminal-sheet extension keeps terminal branch data unchanged. -/
  terminalSheetExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
      x₀ g localModels agreementContinuation.basedWeakHandoffAlong
  /--
  The endpoint of `y`, seen in the source terminal sheet chart, lies in the
  same connected component of the two terminal-chart bases as the source
  terminal cover point.
  -/
  terminalTransitionEndpoint_mem_sameBaseComponent :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x)
      (y : PathHomotopyUniversalCover X x₀)
      (hy : y ∈ (agreementContinuation.basedWeakHandoffAlong p).terminalSheet)
      (_hdeck :
        PathHomotopyUniversalCover.deckAction γ y ∈
          (agreementContinuation.basedWeakHandoffAlong
            ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheet),
      let S := agreementContinuation.basedWeakHandoffAlong p
      let T :=
        agreementContinuation.basedWeakHandoffAlong
          ((agreementContinuation.canonicalLoopFor γ).trans p)
      (⟨PathHomotopyUniversalCover.endpoint y,
        by
          simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using
            PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
              (x₀ := x₀) hy⟩ : S.terminalSheetChart.base) ∈
        connectedComponentIn
          {z : S.terminalSheetChart.base |
            (z : X) ∈ T.terminalSheetChart.base}
          (⟨PathHomotopyUniversalCover.endpoint S.terminalCoverPoint,
            by
              simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using
                PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
                  (x₀ := x₀) S.terminalCoverPoint_mem_terminalSheet⟩ :
            S.terminalSheetChart.base)

/--
Downstairs path data in the terminal sheet-chart base overlap.

This is the path-level version of `BaseSameComponentDataPSL`: for every
deck-compatible terminal endpoint, it provides an actual path in the overlap
of the two selected terminal sheet-chart bases.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionBaseOverlapConnectingPathDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- Coherent terminal-sheet extension keeps terminal branch data unchanged. -/
  terminalSheetExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
      x₀ g localModels agreementContinuation.basedWeakHandoffAlong
  /--
  There is a path in the overlap of the selected terminal sheet-chart bases
  from the source terminal endpoint to the transported endpoint.
  -/
  terminalTransitionBaseOverlapConnectingPath :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x)
      (y : PathHomotopyUniversalCover X x₀)
      (_hy : y ∈ (agreementContinuation.basedWeakHandoffAlong p).terminalSheet)
      (_hdeck :
        PathHomotopyUniversalCover.deckAction γ y ∈
          (agreementContinuation.basedWeakHandoffAlong
            ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheet),
      let S := agreementContinuation.basedWeakHandoffAlong p
      let T :=
        agreementContinuation.basedWeakHandoffAlong
          ((agreementContinuation.canonicalLoopFor γ).trans p)
      ∃ ρ : Path
          (PathHomotopyUniversalCover.endpoint S.terminalCoverPoint)
          (PathHomotopyUniversalCover.endpoint y),
        ∀ t : unitInterval,
          ρ t ∈ S.terminalSheetChart.base ∧
            ρ t ∈ T.terminalSheetChart.base

/--
Upstairs preconnected-overlap data for terminal-transition transport.

This is the weakest cover-geometric version currently exposed: the source
terminal cover point and `y` lie in one preconnected subset of the source
terminal sheet whose deck translate lies in the loop-prepended terminal sheet.
Projecting this subset gives the downstairs preconnected terminal-chart
overlap.
-/
structure PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverPreconnectedOverlapDataPSL
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) where
  /-- Coherent terminal-sheet extension keeps terminal branch data unchanged. -/
  terminalSheetExtensionAgreement :
    PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
      x₀ g localModels agreementContinuation.basedWeakHandoffAlong
  /--
  A preconnected upstairs subset containing the source terminal cover point
  and `y`, inside the source terminal sheet and the deck-preimage of the target
  terminal sheet.
  -/
  terminalTransitionCoverPreconnectedOverlap :
    ∀ (γ : FundamentalGroup X x₀) {x : X} (p : Path x₀ x)
      (y : PathHomotopyUniversalCover X x₀)
      (_hy : y ∈ (agreementContinuation.basedWeakHandoffAlong p).terminalSheet)
      (_hdeck :
        PathHomotopyUniversalCover.deckAction γ y ∈
          (agreementContinuation.basedWeakHandoffAlong
            ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheet),
      ∃ Ω : Set (PathHomotopyUniversalCover X x₀),
        IsPreconnected Ω ∧
        (agreementContinuation.basedWeakHandoffAlong p).terminalCoverPoint ∈ Ω ∧
        y ∈ Ω ∧
        Ω ⊆
          (agreementContinuation.basedWeakHandoffAlong p).terminalSheet ∩
            (PathHomotopyUniversalCover.deckAction γ) ⁻¹'
              (agreementContinuation.basedWeakHandoffAlong
                ((agreementContinuation.canonicalLoopFor γ).trans p)).terminalSheet

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionTransportDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Pure terminal-transition transport plus terminal-sheet extension agreement
give the combined terminal-sheet transport package.
-/
def toTerminalSheetTransportDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionTransportDataPSL
        C)
    (hExtension :
      PathLocalTransitionBasedWeakHandoffTerminalSheetExtensionAgreementPrinciple
        x₀ g localModels C.basedWeakHandoffAlong) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportDataPSL
      C where
  terminalSheetExtensionAgreement := hExtension
  terminalTransitionRepresentativeBetween_terminalSheetExtension_projection_eq :=
    D.terminalTransitionRepresentativeBetween_terminalSheetExtension_projection_eq

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionTransportDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverSameComponentDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Same-component cover-overlap data provide the weaker cover-preconnected
overlap package by taking the connected component of the deck-compatible
terminal-sheet overlap.
-/
noncomputable def toCoverPreconnectedOverlapDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverSameComponentDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverPreconnectedOverlapDataPSL
      C where
  terminalSheetExtensionAgreement := D.terminalSheetExtensionAgreement
  terminalTransitionCoverPreconnectedOverlap := by
    intro γ x p y hy hdeck
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong ((C.canonicalLoopFor γ).trans p)
    let Ω : Set (PathHomotopyUniversalCover X x₀) :=
      connectedComponentIn
        (S.terminalSheet ∩
          (PathHomotopyUniversalCover.deckAction γ) ⁻¹' T.terminalSheet)
        S.terminalCoverPoint
    have hSource :
        S.terminalCoverPoint ∈
          S.terminalSheet ∩
            (PathHomotopyUniversalCover.deckAction γ) ⁻¹' T.terminalSheet := by
      refine ⟨S.terminalCoverPoint_mem_terminalSheet, ?_⟩
      simpa [S, T] using
        C.terminalCoverPoint_mem_deck_preimage_canonicalLoop_terminalSheet γ p
    refine
      ⟨Ω, isPreconnected_connectedComponentIn,
        mem_connectedComponentIn hSource, ?_, ?_⟩
    · simpa [Ω, S, T] using
        D.terminalTransitionEndpoint_mem_sameCoverComponent γ p y hy hdeck
    · intro z hz
      simpa [Ω, S, T] using
        connectedComponentIn_subset
          (S.terminalSheet ∩
            (PathHomotopyUniversalCover.deckAction γ) ⁻¹' T.terminalSheet)
          S.terminalCoverPoint hz

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverSameComponentDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionBaseSameComponentDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Downstairs base-component terminal-transition data imply the intrinsic
upstairs cover-component data.
-/
noncomputable def toCoverSameComponentDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionBaseSameComponentDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverSameComponentDataPSL
      C where
  terminalSheetExtensionAgreement := D.terminalSheetExtensionAgreement
  terminalTransitionEndpoint_mem_sameCoverComponent := by
    intro γ x p y hy hdeck
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong ((C.canonicalLoopFor γ).trans p)
    have hbase :=
      D.terminalTransitionEndpoint_mem_sameBaseComponent γ p y hy hdeck
    have hsourceDeck :
        PathHomotopyUniversalCover.deckAction γ S.terminalCoverPoint ∈
          T.terminalSheet := by
      simpa [S, T] using
        C.terminalCoverPoint_mem_deck_preimage_canonicalLoop_terminalSheet γ p
    have hcover :
        y ∈ connectedComponentIn
          (S.terminalSheetChart.sheet ∩
            (PathHomotopyUniversalCover.deckAction γ) ⁻¹'
              T.terminalSheetChart.sheet)
          S.terminalCoverPoint := by
      exact
        PathHomotopyUniversalCover.mem_connectedComponentIn_localSheetChart_inter_deck_preimage_of_endpoint_mem_base_inter
          (x₀ := x₀) γ S.terminalSheetChart T.terminalSheetChart
          (by
            simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using
              S.terminalCoverPoint_mem_terminalSheet)
          (by
            simpa [T, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using
              hsourceDeck)
          (by
            simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using
              hy)
          (by
            simpa [S, T] using hbase)
    simpa [S, T, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using hcover

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionBaseSameComponentDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionBaseOverlapConnectingPathDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
An explicit path in the overlap of the two selected terminal sheet-chart bases
implies the base-same-component boundary.
-/
noncomputable def toBaseSameComponentDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionBaseOverlapConnectingPathDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionBaseSameComponentDataPSL
      C where
  terminalSheetExtensionAgreement := D.terminalSheetExtensionAgreement
  terminalTransitionEndpoint_mem_sameBaseComponent := by
    intro γ x p y hy hdeck
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong ((C.canonicalLoopFor γ).trans p)
    rcases D.terminalTransitionBaseOverlapConnectingPath γ p y hy hdeck with
      ⟨ρ, hρ⟩
    let a : S.terminalSheetChart.base :=
      ⟨PathHomotopyUniversalCover.endpoint S.terminalCoverPoint,
        by
          simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using
            PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
              (x₀ := x₀) S.terminalCoverPoint_mem_terminalSheet⟩
    let b : S.terminalSheetChart.base :=
      ⟨PathHomotopyUniversalCover.endpoint y,
        by
          simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using
            PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
              (x₀ := x₀) hy⟩
    let ρS : Path a b :=
      { toFun := fun t => ⟨ρ t, (hρ t).1⟩
        continuous_toFun := by
          exact Continuous.subtype_mk ρ.continuous (fun t => (hρ t).1)
        source' := by
          apply Subtype.ext
          exact ρ.source
        target' := by
          apply Subtype.ext
          exact ρ.target }
    have hρS :
        ∀ t : unitInterval,
          ρS t ∈ {z : S.terminalSheetChart.base |
            (z : X) ∈ T.terminalSheetChart.base} := by
      intro t
      exact (hρ t).2
    simpa [S, T, a, b, ρS] using
      PathLocalTransitionModelBasedWeakHandoffSkeleton.path_target_mem_connectedComponentIn_of_forall_mem
        (X := S.terminalSheetChart.base) ρS hρS

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionBaseOverlapConnectingPathDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverPreconnectedOverlapDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
An upstairs preconnected deck-compatible terminal-sheet overlap projects to a
downstairs preconnected terminal-chart overlap.
-/
noncomputable def toPreconnectedOverlapDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverPreconnectedOverlapDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionPreconnectedOverlapDataPSL
      C where
  terminalSheetExtensionAgreement := D.terminalSheetExtensionAgreement
  terminalTransitionPreconnectedOverlap := by
    intro γ x p y hy hdeck
    let L := C.canonicalLoopFor γ
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong (L.trans p)
    rcases D.terminalTransitionCoverPreconnectedOverlap γ p y hy hdeck with
      ⟨Ω, hΩpre, hSΩ, hyΩ, hΩsub⟩
    let W : Set X :=
      PathHomotopyUniversalCover.endpoint '' Ω
    have hWpre : IsPreconnected W :=
      hΩpre.image PathHomotopyUniversalCover.endpoint
        (PathHomotopyUniversalCover.continuous_endpoint (x₀ := x₀)).continuousOn
    have hxW : x ∈ W := by
      refine ⟨S.terminalCoverPoint, hSΩ, ?_⟩
      simp [S]
    have hyW : PathHomotopyUniversalCover.endpoint y ∈ W :=
      ⟨y, hyΩ, rfl⟩
    have hWsub :
        W ⊆
          (localModels.chartAt S.terminalCenter).domain ∩
            (localModels.chartAt T.terminalCenter).domain := by
      intro z hz
      rcases hz with ⟨η, hηΩ, rfl⟩
      have hη := hΩsub hηΩ
      have hSdomain :
          PathHomotopyUniversalCover.endpoint η ∈
            (localModels.chartAt S.terminalCenter).domain :=
        S.endpoint_mem_terminal_domain_of_mem_terminalSheet hη.1
      have hTdeck :
          PathHomotopyUniversalCover.endpoint
              (PathHomotopyUniversalCover.deckAction γ η) ∈
            (localModels.chartAt T.terminalCenter).domain :=
        T.endpoint_mem_terminal_domain_of_mem_terminalSheet hη.2
      have hTdomain :
          PathHomotopyUniversalCover.endpoint η ∈
            (localModels.chartAt T.terminalCenter).domain := by
        simpa [PathHomotopyUniversalCover.endpoint_deckAction] using hTdeck
      exact ⟨hSdomain, hTdomain⟩
    exact ⟨W, hWpre, hxW, hyW, by simpa [W, S, T, L] using hWsub⟩

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverPreconnectedOverlapDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapConnectingPathDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
An explicit path in the terminal-chart overlap implies the same-component
boundary.
-/
noncomputable def toSameOverlapComponentDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapConnectingPathDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionSameOverlapComponentDataPSL
      C where
  terminalSheetExtensionAgreement := D.terminalSheetExtensionAgreement
  terminalTransitionEndpoint_mem_sameOverlapComponent := by
    intro γ x p y hy hdeck
    rcases D.terminalTransitionOverlapConnectingPath γ p y hy hdeck with
      ⟨ρ, hρ⟩
    simpa using
      PathLocalTransitionModelBasedWeakHandoffSkeleton.path_target_mem_connectedComponentIn_of_forall_mem
        (X := X) ρ hρ

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapConnectingPathDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverOverlapPathDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
An upstairs path in the deck-compatible terminal-sheet overlap projects to a
path in the fixed terminal-chart overlap downstairs.
-/
noncomputable def toOverlapConnectingPathDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverOverlapPathDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapConnectingPathDataPSL
      C where
  terminalSheetExtensionAgreement := D.terminalSheetExtensionAgreement
  terminalTransitionOverlapConnectingPath := by
    intro γ x p y hy hdeck
    let L := C.canonicalLoopFor γ
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong (L.trans p)
    rcases D.terminalTransitionCoverOverlapPath γ p y hy hdeck with
      ⟨κ, hκ⟩
    let ρ : Path x (PathHomotopyUniversalCover.endpoint y) :=
      (κ.map (PathHomotopyUniversalCover.continuous_endpoint (x₀ := x₀))).cast
        S.endpoint_terminalCoverPoint rfl
    refine ⟨ρ, ?_⟩
    intro t
    have hS :
        PathHomotopyUniversalCover.endpoint (κ t) ∈
          (localModels.chartAt S.terminalCenter).domain :=
      S.endpoint_mem_terminal_domain_of_mem_terminalSheet (hκ t).1
    have hTdeck :
        PathHomotopyUniversalCover.endpoint
            (PathHomotopyUniversalCover.deckAction γ (κ t)) ∈
          (localModels.chartAt T.terminalCenter).domain :=
      T.endpoint_mem_terminal_domain_of_mem_terminalSheet (hκ t).2
    have hT :
        PathHomotopyUniversalCover.endpoint (κ t) ∈
          (localModels.chartAt T.terminalCenter).domain := by
      simpa [PathHomotopyUniversalCover.endpoint_deckAction] using hTdeck
    exact ⟨by simpa [ρ], by simpa [ρ] using hT⟩

/--
An upstairs path in the deck-compatible terminal-sheet overlap projects to a
path in the overlap of the two selected terminal sheet-chart bases.
-/
noncomputable def toBaseOverlapConnectingPathDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverOverlapPathDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionBaseOverlapConnectingPathDataPSL
      C where
  terminalSheetExtensionAgreement := D.terminalSheetExtensionAgreement
  terminalTransitionBaseOverlapConnectingPath := by
    intro γ x p y hy hdeck
    let L := C.canonicalLoopFor γ
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong (L.trans p)
    rcases D.terminalTransitionCoverOverlapPath γ p y hy hdeck with
      ⟨κ, hκ⟩
    let ρ : Path
        (PathHomotopyUniversalCover.endpoint S.terminalCoverPoint)
        (PathHomotopyUniversalCover.endpoint y) :=
      κ.map (PathHomotopyUniversalCover.continuous_endpoint (x₀ := x₀))
    refine ⟨ρ, ?_⟩
    intro t
    refine ⟨?_, ?_⟩
    · simpa [ρ, S, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using
        PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
          (x₀ := x₀) (hκ t).1
    · have hTbase :
          PathHomotopyUniversalCover.endpoint
              (PathHomotopyUniversalCover.deckAction γ (κ t)) ∈
            T.terminalSheetChart.base := by
        simpa [T, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalSheet] using
          PathHomotopyUniversalCover.endpoint_mem_of_mem_localSheet
            (x₀ := x₀) (hκ t).2
      simpa [ρ, PathHomotopyUniversalCover.endpoint_deckAction] using hTbase

/--
An upstairs path in the deck-compatible terminal-sheet overlap puts the
endpoint in the same connected component of that overlap.
-/
noncomputable def toCoverSameComponentDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverOverlapPathDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverSameComponentDataPSL
      C where
  terminalSheetExtensionAgreement := D.terminalSheetExtensionAgreement
  terminalTransitionEndpoint_mem_sameCoverComponent := by
    intro γ x p y hy hdeck
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong ((C.canonicalLoopFor γ).trans p)
    rcases D.terminalTransitionCoverOverlapPath γ p y hy hdeck with
      ⟨κ, hκ⟩
    have hRangePre : IsPreconnected (Set.range κ) :=
      isPreconnected_range κ.continuous
    have hRangeSub :
        Set.range κ ⊆
          S.terminalSheet ∩
            (PathHomotopyUniversalCover.deckAction γ) ⁻¹' T.terminalSheet := by
      intro z hz
      rcases hz with ⟨t, rfl⟩
      exact hκ t
    have hSub :
        Set.range κ ⊆
          connectedComponentIn
            (S.terminalSheet ∩
              (PathHomotopyUniversalCover.deckAction γ) ⁻¹' T.terminalSheet)
            S.terminalCoverPoint :=
      hRangePre.subset_connectedComponentIn (Path.source_mem_range κ) hRangeSub
    simpa [S, T] using hSub (Path.target_mem_range κ)

/--
An upstairs path in the deck-compatible terminal-sheet overlap gives the
weaker upstairs preconnected-overlap package by taking the range of the path.
-/
noncomputable def toCoverPreconnectedOverlapDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverOverlapPathDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverPreconnectedOverlapDataPSL
      C where
  terminalSheetExtensionAgreement := D.terminalSheetExtensionAgreement
  terminalTransitionCoverPreconnectedOverlap := by
    intro γ x p y hy hdeck
    rcases D.terminalTransitionCoverOverlapPath γ p y hy hdeck with
      ⟨κ, hκ⟩
    refine
      ⟨Set.range κ, isPreconnected_range κ.continuous,
        Path.source_mem_range κ, Path.target_mem_range κ, ?_⟩
    intro z hz
    rcases hz with ⟨t, rfl⟩
    exact hκ t

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverOverlapPathDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapPathDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
If the chosen source terminal-sheet path stays in the target terminal chart,
then it is an explicit path in the fixed terminal-chart overlap.
-/
noncomputable def toOverlapConnectingPathDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapPathDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapConnectingPathDataPSL
      C where
  terminalSheetExtensionAgreement := D.terminalSheetExtensionAgreement
  terminalTransitionOverlapConnectingPath := by
    intro γ x p y hy hdeck
    let L := C.canonicalLoopFor γ
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong (L.trans p)
    refine ⟨S.terminalSheetPathInSet hy, ?_⟩
    intro t
    refine ⟨?_, ?_⟩
    · simpa [S] using S.terminalSheetPathInSet_mem_terminal_domain hy t
    · simpa [S, T, L] using
        D.terminalSheetPath_mem_targetTerminalDomain γ p y hy hdeck t

/--
Terminal-sheet overlap-path data imply the same-overlap-component boundary.
-/
noncomputable def toSameOverlapComponentDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapPathDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionSameOverlapComponentDataPSL
      C :=
  D.toOverlapConnectingPathDataPSL.toSameOverlapComponentDataPSL

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapPathDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionSameOverlapComponentDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Same-component overlap data provide the preconnected-overlap package by taking
the connected component of the fixed terminal-chart overlap.
-/
noncomputable def toPreconnectedOverlapDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionSameOverlapComponentDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionPreconnectedOverlapDataPSL
      C where
  terminalSheetExtensionAgreement := D.terminalSheetExtensionAgreement
  terminalTransitionPreconnectedOverlap := by
    intro γ x p y hy hdeck
    let L := C.canonicalLoopFor γ
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong (L.trans p)
    let overlap : Set X :=
      (localModels.chartAt S.terminalCenter).domain ∩
        (localModels.chartAt T.terminalCenter).domain
    have hxOverlap : x ∈ overlap := by
      refine ⟨?_, ?_⟩
      · simpa [S, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalCenter]
          using S.terminal_endpoint_mem_domain
      · simpa [T, L, PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalCenter]
          using T.terminal_endpoint_mem_domain
    refine
      ⟨connectedComponentIn overlap x, isPreconnected_connectedComponentIn,
        mem_connectedComponentIn hxOverlap, ?_, ?_⟩
    · simpa [overlap, S, T, L] using
        D.terminalTransitionEndpoint_mem_sameOverlapComponent γ p y hy hdeck
    · intro z hz
      simpa [overlap, S, T, L] using
        connectedComponentIn_subset overlap x hz

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionSameOverlapComponentDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionPreconnectedOverlapDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Preconnected terminal-chart overlap data imply terminal-sheet transport of the
normalized canonical-loop transition class.
-/
noncomputable def toTerminalSheetTransportDataPSL
    (D :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionPreconnectedOverlapDataPSL
        C) :
    PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalSheetTransportDataPSL
      C where
  terminalSheetExtensionAgreement := D.terminalSheetExtensionAgreement
  terminalTransitionRepresentativeBetween_terminalSheetExtension_projection_eq := by
    intro γ x p y hy hdeck
    classical
    let L := C.canonicalLoopFor γ
    let S := C.basedWeakHandoffAlong p
    let T := C.basedWeakHandoffAlong (L.trans p)
    let σ := S.terminalSheetPathInSet hy
    let q : Path x₀ (PathHomotopyUniversalCover.endpoint y) := p.trans σ
    let τ := T.terminalSheetPathInSet
      (y' := PathHomotopyUniversalCover.deckAction γ y) hdeck
    let r : Path x₀ (PathHomotopyUniversalCover.endpoint y) := (L.trans p).trans τ
    rcases D.terminalSheetExtensionAgreement p hy with ⟨hSourceExt⟩
    rcases D.terminalSheetExtensionAgreement (L.trans p) hdeck with ⟨hTargetExt⟩
    rcases
        D.terminalTransitionPreconnectedOverlap γ p y hy hdeck with
      ⟨W, hWpre, hxW, hyW, hWsub⟩
    let Tx := C.terminalTransitionDataBetween p (L.trans p)
    let Ty₀ := C.terminalTransitionDataBetween q r
    let Ty :
        HyperbolicLocalChart.LocalRealMobiusTransitionData
          (localModels.chartAt S.terminalCenter)
          (localModels.chartAt T.terminalCenter)
          (PathHomotopyUniversalCover.endpoint y) :=
      localRealMobiusTransitionData_congr
        (congrArg localModels.chartAt hSourceExt.terminalCenter_eq).symm
        (congrArg localModels.chartAt hTargetExt.terminalCenter_eq).symm
        rfl Ty₀
    have hWexists :
        ∀ ⦃z : X⦄, z ∈ W →
          Nonempty
            (HyperbolicLocalChart.LocalRealMobiusTransitionData
              (localModels.chartAt S.terminalCenter)
              (localModels.chartAt T.terminalCenter) z) := by
      intro z hz
      have hzOverlap :
          z ∈
            (localModels.chartAt S.terminalCenter).domain ∩
              (localModels.chartAt T.terminalCenter).domain := by
        simpa [S, T, L] using hWsub hz
      exact
        localModels.transition_localRealMobius S.terminalCenter
          T.terminalCenter z hzOverlap
    have hConst :
        realMobiusProjection Ty.representative =
          realMobiusProjection Tx.representative :=
      localRealMobiusTransitionData_projection_eq_of_preconnected
        hWpre hWexists hxW hyW Tx Ty
    simpa [Tx, Ty, Ty₀, q, r, L, S, T,
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData.terminalTransitionRepresentativeBetween]
      using hConst

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionPreconnectedOverlapDataPSL

end HyperbolicMetric

end

end JJMath
