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






namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionAgreementData

namespace PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffElementaryGridExtensionProjectionAgreementData

/--
The terminal-sheet homotopy principle fills the agreement record.  The only
cover-theoretic input is that a point in a terminal sheet is represented by
the continued path followed by the canonical local path in that sheet.

%%handwave
name: The terminal-sheet homotopy principle fills the agreement data
statement:
  The terminal-sheet homotopy principle fills the agreement data. The only cover-theoretic input
  is that a point in a terminal sheet is represented by the continued path followed by the
  canonical local path in that sheet.
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

/-- At the represented terminal point, the terminal branch value is `dev`.

%%handwave
name: The developing map equals the terminal value at a represented lift
statement: For every path $p:x_0\rightsquigarrow x$, the terminal branch value produced along $p$ equals the single-valued developing map at the lift $(x,[p])$: $v(p)=\mathrm{dev}(x,[p])$.
proof: The lift $(x,[p])$ belongs to the terminal sheet of $p$. Evaluate the assumed sheetwise developing formula there and identify its endpoint with $x$.
-/
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

%%handwave
name: Homotopic paths have equal terminal values
statement: If paths $p,q:x_0\rightsquigarrow x$ are homotopic relative to endpoints, then their terminal continuation values coincide: $v(p)=v(q)$.
proof: Each terminal value equals the developing map at its terminal lift, and homotopic paths determine the same lift in the path-homotopy cover.
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

%%handwave
name: Terminal formulas agree for two representatives of a sheet point
statement: Let $y$ lie in the terminal sheet of $p$ and let $p':x_0\rightsquigarrow\pi(y)$ represent the path class of $y$. Then the terminal formula obtained along $p'$ and the terminal-sheet formula obtained along $p$ have the same value at $\pi(y)$.
proof: The terminal lift of $p'$ is $y$, hence $y$ also lies in the terminal sheet selected for $p'$. The developing-map formula on the two terminal sheets identifies both branch values with $\mathrm{dev}(y)$.
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

%%handwave
name: Cover-level PSL continuation gives canonical-terminal-sheet value continuation
statement:
  Cover-level PSL continuation gives canonical-terminal-sheet value continuation.
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

%%handwave
name: The canonical representative loop used to read off loop monodromy from terminal continuation
statement:
  The canonical representative loop used to read off loop monodromy from terminal continuation.
  The convention matches deck actions in this file: loop-prepending represents γ⁻¹ at the
  path-class level.
-/
noncomputable def canonicalLoopFor
    (_C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) : Path x₀ x₀ :=
  Quot.out (FundamentalGroup.toPath γ⁻¹)

/-- The canonical representative loop has the required path class.

%%handwave
name: Path class of the canonical loop representative
statement: For every $\gamma\in\pi_1(X,x_0)$, the chosen canonical loop $L_\gamma$ represents $\gamma^{-1}$: $[L_\gamma]=\gamma^{-1}$.
proof: The loop is chosen as a representative of the quotient path class $\gamma^{-1}$, so the quotient map returns that class.
-/
theorem canonicalLoopFor_spec
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels)
    (γ : FundamentalGroup X x₀) :
    Path.Homotopic.Quotient.mk (C.canonicalLoopFor γ) =
      FundamentalGroup.toPath γ⁻¹ :=
  Quot.out_eq (FundamentalGroup.toPath γ⁻¹)

/-- The base path used to normalize terminal Mobius products.

%%handwave
name: The base path used to normalize terminal Möbius products
statement:
  The base path used to normalize terminal Möbius products.
-/
def baseNormalizationPath
    (_C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) : Path x₀ x₀ :=
  Path.refl x₀

/-- The terminal PSL class of the normalized base path.

%%handwave
name: The terminal PSL class of the normalized base path
statement:
  The terminal PSL class of the normalized base path.
-/
noncomputable def baseTerminalProjection
    (C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels) : RealMobiusGroup :=
  realMobiusProjection
    ((C.basedWeakHandoffAlong C.baseNormalizationPath).terminalMobius)

/--
The adjusted terminal PSL class obtained by continuing around the canonical
representative of `γ⁻¹` and then back along the base normalization path.

%%handwave
name: The adjusted terminal PSL class obtained by continuing around the canonical representative of γ⁻¹ and then back along the base normalization path
statement:
  The adjusted terminal PSL class obtained by continuing around the canonical representative of
  γ⁻¹ and then back along the base normalization path.
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

%%handwave
name: The PSL holonomy candidate read off from loop terminal continuation, normalized by the base terminal class
statement:
  The PSL holonomy candidate read off from loop terminal continuation, normalized by the base
  terminal class.
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

%%handwave
name: Reconstruction of the adjusted loop class from normalized holonomy
statement: If $B$ is the base terminal projective class, $A_\gamma$ the adjusted loop-terminal class, and $H_\gamma=A_\gamma B^{-1}$, then $A_\gamma=H_\gamma B$.
proof: Expand the definition of $H_\gamma$ and cancel $B^{-1}B$.
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

%%handwave
name: Canonical-loop covariance at the base normalization path
statement: For the constant base path $e$, the adjusted terminal class after prepending $L_\gamma$ satisfies $[M_{L_\gamma*e}A(e,L_\gamma*e)]=H_\gamma[M_e]$.
proof: Replace the chosen canonical-loop endpoint transition by the transition between the two terminal skeletons, whose projective classes agree. The result is the defining adjusted loop class, and its normalization formula gives $H_\gamma[M_e]$.
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

%%handwave
name: The normalized canonical-loop terminal PSL class at a terminal path p
statement:
  The normalized canonical-loop terminal PSL class at a terminal path p. This quotient removes
  the terminal Möbius class of p; the monodromy theorem says that the resulting class is
  independent of p and hence equals its base value.
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

%%handwave
name: Normalized loop transport at the base is the derived holonomy
statement: For the constant base path $e$, the normalized canonical-loop class is $N_\gamma(e)=H_\gamma$.
proof: Canonical-loop covariance at $e$ gives the numerator $H_\gamma[M_e]$; multiplying by $[M_e]^{-1}$ cancels the base class.
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

%%handwave
name: Homotopy invariance of normalized canonical-loop transport
statement: If $p,q:x_0\rightsquigarrow x$ are endpoint-fixed homotopic, then $N_\gamma(p)=N_\gamma(q)$.
proof: Compare terminal products of $p$ and $q$ through their transition class, and do the same after prepending $L_\gamma$. Homotopy invariance gives compatible adjusted products; transition composition then cancels the intermediate class in the normalized quotient.
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

%%handwave
name: The normalized canonical-loop terminal class as a function on the canonical path-homotopy cover
statement:
  The normalized canonical-loop terminal class as a function on the canonical path-homotopy
  cover.
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

%%handwave
name: Evaluation of normalized loop transport on a represented cover point
statement: For a lift represented by $p:x_0\rightsquigarrow x$, the cover-valued normalized transport equals the path formula: $N_\gamma(x,[p])=N_\gamma(p)$.
proof: The chosen quotient representative of $[p]$ is endpoint-fixed homotopic to $p$, and the path formula is homotopy invariant.
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
Constancy of the cover-valued normalized projection implies propagation of the
path-representative normalized projection from the base path.

%%handwave
name: Coverwise constancy propagates normalized loop transport from the base
statement: If $N_\gamma(y)=N_\gamma(\widetilde x_0)$ for every cover point $y$, then $N_\gamma(p)=N_\gamma(e)$ for every based path $p$, where $e$ is the constant base path.
proof: Evaluate the cover function at the lift represented by $p$, apply the assumed constancy, and represent the base lift by $e$.
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

%%handwave
name: Propagation of normalized transport implies canonical-loop covariance
statement: If $N_\gamma(p)=N_\gamma(e)$ for every based path $p$, then $[M_{L_\gamma*p}A(p,L_\gamma*p)]=H_\gamma[M_p]$.
proof: The propagation hypothesis and the base computation give $A_p[M_p]^{-1}=H_\gamma$ for the adjusted numerator $A_p$. Multiply on the right by $[M_p]$ and cancel.
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

%%handwave
name: Canonical-loop covariance implies covariance for every representative loop
statement: Suppose $[M_{L_\gamma*p}A(p,L_\gamma*p)]=H_\gamma[M_p]$ for the chosen canonical loop $L_\gamma$. Then the same formula holds for every loop $L$ representing $\gamma^{-1}$, using the automatic endpoint transition from $p$ to $L*p$.
proof: The loops $L$ and $L_\gamma$ are endpoint-fixed homotopic, hence so are their concatenations with $p$. Homotopy invariance of adjusted terminal classes replaces the arbitrary loop-prepended path by the canonical one, after which canonical-loop covariance applies.
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

%%handwave
name: Canonical-terminal-sheet based weak handoff continuation plus PSL loop equivariance gives PSL path-class monodromy
statement:
  Canonical-terminal-sheet based weak handoff continuation plus PSL loop equivariance gives PSL
  path-class monodromy.
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

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementValueEquivarianceDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData







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

%%handwave
name: Terminal-sheet agreement data automatically has nonempty-open terminal coordinate agreement sets
statement:
  Terminal-sheet agreement data automatically has nonempty-open terminal coordinate agreement
  sets.
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

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaProjectionFaithfulnessDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalFormulaNonemptyOpenAgreementDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

/--
Nonempty open agreement sets give three-point richness.

%%handwave
name: Nonempty open agreement sets give three-point richness
statement:
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

/-- Three-point richness gives terminal-coordinate action faithfulness.

%%handwave
name: Three-point richness gives terminal-coordinate action faithfulness
statement:
  Three-point richness gives terminal-coordinate action faithfulness.
-/
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

%%handwave
name: Action faithfulness on the coordinate agreement set gives terminal-formula projection faithfulness
statement:
  Action faithfulness on the coordinate agreement set gives terminal-formula projection
  faithfulness.
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

%%handwave
name: Terminal-sheet agreement data automatically has three-point-rich terminal coordinate agreement sets
statement:
  Terminal-sheet agreement data automatically has three-point-rich terminal coordinate agreement
  sets.
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

%%handwave
name: Terminal-sheet agreement data automatically has PSL action faithfulness on the terminal coordinate agreement sets
statement:
  Terminal-sheet agreement data automatically has PSL action faithfulness on the terminal
  coordinate agreement sets.
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

%%handwave
name: Terminal-sheet agreement data automatically has PSL projection faithfulness for the transition-adjusted terminal formulae
statement:
  Terminal-sheet agreement data automatically has PSL projection faithfulness for the
  transition-adjusted terminal formulae.
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
Null-homotopic loop-prepending has trivial adjusted terminal PSL effect.

This is the identity-loop part of monodromy at arbitrary endpoints.  It uses
only terminal-sheet agreement: when `γ = 1`, the deck action is the identity,
so the source and loop-prepended terminal formulae compute the same upstairs
value on their common terminal-sheet patch.

%%handwave
name: A null-homotopic loop has trivial adjusted terminal class
statement: If a loop $L$ represents the identity element of $\pi_1(X,x_0)$, then for every based path $p$ the adjusted class satisfies $[M_{L*p}A(p,L*p)]=[M_p]$.
proof: Deck action by the identity fixes every cover point. On the common terminal-sheet coordinate patch, the source formula and the transition-adjusted loop-prepended formula therefore both equal the same developing-map value. Faithfulness of the projective Möbius action on that open coordinate set forces equality of their projective classes.
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

%%handwave
name: The derived holonomy sends the identity to one
statement: The normalized loop-terminal assignment satisfies $H_1=1$.
proof: Apply triviality of the adjusted terminal class to the canonical representative of the identity and the base normalization path. The adjusted numerator equals the base class, so multiplication by the inverse base class gives $1$.
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

%%handwave
name: Covariance forces multiplicativity of the derived holonomy
statement: If every loop $L$ representing $\gamma^{-1}$ satisfies $[M_{L*p}A(p,L*p)]=H_\gamma[M_p]$, then $H_{\gamma\delta}=H_\gamma H_\delta$.
proof: Compare direct prepending by a representative of $(\gamma\delta)^{-1}$ with successive prepending by representatives of $\delta^{-1}$ and $\gamma^{-1}$. Transition composition identifies the two adjusted chart changes, while homotopy invariance identifies the parenthesized concatenations. Applying covariance twice gives $H_\gamma H_\delta$ times the base class; applying it once gives $H_{\gamma\delta}$ times the same class, which cancels.
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




namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverSameComponentDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverSameComponentDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionBaseSameComponentDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionBaseSameComponentDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionBaseOverlapConnectingPathDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionBaseOverlapConnectingPathDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverPreconnectedOverlapDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverPreconnectedOverlapDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapConnectingPathDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapConnectingPathDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverOverlapPathDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionCoverOverlapPathDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapPathDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionOverlapPathDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionSameOverlapComponentDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionSameOverlapComponentDataPSL

namespace PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionPreconnectedOverlapDataPSL

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {C :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g localModels}

end PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionTerminalTransitionPreconnectedOverlapDataPSL

end HyperbolicMetric

end

end JJMath
