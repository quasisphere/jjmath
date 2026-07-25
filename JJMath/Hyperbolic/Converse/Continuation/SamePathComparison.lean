import JJMath.Hyperbolic.Converse.Continuation.GridHomotopy

/-!
# Split analytic continuation targets for the partial converse
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

namespace PathLocalTransitionModelBasedWeakHandoffTerminalExtensionAgreement

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}
    {S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    {y' : PathHomotopyUniversalCover X x₀}
    {hy' : y' ∈ S.terminalSheet}
    {T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
        (p.trans (S.terminalSheetPathInSet hy'))}

/--
Terminal chart/Mobius agreement gives terminal branch-formula agreement at
the extended endpoint.

%%handwave
name: Terminal formulas agree under exact terminal extension data
statement: Let $y$ lie in the terminal sheet of a continuation skeleton $S$, and let $T$ continue $S$ to the endpoint $\pi(y)$. If $T$ has the same terminal chart and accumulated Möbius transformation as $S$, then $F_T(\pi(y))=F_S(\pi(y))$.
proof: Expand both terminal formulas as the accumulated real Möbius action on the terminal chart coordinate, then substitute the equal terminal chart centers and Möbius transformations.
-/
theorem terminalFormulaAt_eq
    (A :
      PathLocalTransitionModelBasedWeakHandoffTerminalExtensionAgreement
        S hy' T) :
    T.terminalFormulaAt (PathHomotopyUniversalCover.endpoint y') =
      S.terminalFormulaAt (PathHomotopyUniversalCover.endpoint y') := by
  change
    realMobiusRepresentativeAction T.terminalMobius
        ((localModels.chartAt T.terminalCenter).toUpperHalfPlane
          (PathHomotopyUniversalCover.endpoint y')) =
      realMobiusRepresentativeAction S.terminalMobius
        ((localModels.chartAt S.terminalCenter).toUpperHalfPlane
          (PathHomotopyUniversalCover.endpoint y'))
  rw [A.terminalCenter_eq, A.terminalMobius_eq]

end PathLocalTransitionModelBasedWeakHandoffTerminalExtensionAgreement


namespace PathLocalTransitionModelBasedWeakHandoffSkeleton

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}

/-- The explicit terminal-extension skeleton carries terminal-extension agreement data.

%%handwave
name: The explicit terminal-extension skeleton carries terminal-extension agreement data
statement:
  The explicit terminal-extension skeleton carries terminal-extension agreement data.
-/
def terminalExtensionSkeletonAgreement
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    PathLocalTransitionModelBasedWeakHandoffTerminalExtensionAgreement S hy'
      (S.terminalExtensionSkeleton hy') where
  terminalCenter_eq := S.terminalExtensionSkeleton_terminalCenter hy'
  terminalMobius_eq := S.terminalExtensionSkeleton_terminalMobius_eq hy'

/--
The explicit terminal-extension skeleton gives the same terminal formula at
the extended endpoint.

%%handwave
name: The explicit terminal extension preserves the branch value
statement: For a skeleton $S$ and a lift $y$ in its terminal sheet, the explicit skeleton extending along the sheet path satisfies $F_{S_y}(\pi(y))=F_S(\pi(y))$.
proof: The explicit extension has the same terminal center and accumulated Möbius transformation as $S$, so apply [exact terminal extension data identify the two endpoint formulas](lean:JJMath.HyperbolicMetric.PathLocalTransitionModelBasedWeakHandoffTerminalExtensionAgreement.terminalFormulaAt_eq).
-/
theorem terminalExtensionSkeleton_terminalFormulaAt_eq
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀}
    (hy' : y' ∈ S.terminalSheet) :
    (S.terminalExtensionSkeleton hy').terminalFormulaAt
        (PathHomotopyUniversalCover.endpoint y') =
      S.terminalFormulaAt (PathHomotopyUniversalCover.endpoint y') :=
  PathLocalTransitionModelBasedWeakHandoffTerminalExtensionAgreement.terminalFormulaAt_eq
    (S.terminalExtensionSkeletonAgreement hy')

end PathLocalTransitionModelBasedWeakHandoffSkeleton

/--
Unconditional existential terminal-sheet local extension.

This avoids imposing coherence on an arbitrary global choice of path
skeletons: given any terminal sheet point, there exists an appended skeleton
whose terminal branch formula is the same at the new endpoint.

%%handwave
name: Unconditional existential terminal-sheet local extension
statement:
  Unconditional existential terminal-sheet local extension. This avoids imposing coherence on an
  arbitrary global choice of path skeletons: given any terminal sheet point, there exists an
  appended skeleton whose terminal branch formula is the same at the new endpoint.
-/
def PathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionExistencePrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x : X} {p : Path x₀ x}
    (S : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    {y' : PathHomotopyUniversalCover X x₀} (hy' : y' ∈ S.terminalSheet),
      ∃ T :
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
          (p.trans (S.terminalSheetPathInSet hy')),
        T.terminalFormulaAt (PathHomotopyUniversalCover.endpoint y') =
          S.terminalFormulaAt (PathHomotopyUniversalCover.endpoint y')

/-- The explicit terminal-extension skeleton proves existential local extension.

%%handwave
name: A terminal-sheet path admits a value-preserving continuation skeleton
statement: For every continuation skeleton $S$ over $p:x_0\rightsquigarrow x$ and every lift $y$ in its terminal sheet, there is a skeleton $T$ over the path obtained by appending the sheet path to $\pi(y)$ such that $F_T(\pi(y))=F_S(\pi(y))$.
proof: Choose the explicit terminal-extension skeleton and use [its endpoint branch value equals the original branch value](lean:JJMath.HyperbolicMetric.PathLocalTransitionModelBasedWeakHandoffSkeleton.terminalExtensionSkeleton_terminalFormulaAt_eq).
-/
theorem pathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionExistencePrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    PathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionExistencePrinciple
      x₀ g localModels := by
  intro x p S y' hy'
  exact
    ⟨S.terminalExtensionSkeleton hy',
      S.terminalExtensionSkeleton_terminalFormulaAt_eq hy'⟩

/--
Same-path uniqueness for based weak handoff skeletons.

This is the remaining choice-independence needed to turn explicit
terminal-sheet extensions into compatibility for an arbitrary global choice of
skeletons: two skeletons carried by the same representative path have the
same terminal value.

%%handwave
name: Same-path uniqueness for based weak handoff skeletons
statement:
  Same-path uniqueness for based weak handoff skeletons. This is the remaining
  choice-independence needed to turn explicit terminal-sheet extensions into compatibility for
  an arbitrary global choice of skeletons: two skeletons carried by the same representative path
  have the same terminal value.
-/
def PathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x : X} {p : Path x₀ x}
    (S T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p),
      S.terminalValue = T.terminalValue

namespace PathLocalTransitionBasedWeakHandoffElementaryGridMove

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    {x : X} {p q : Path x₀ x}

omit [RiemannSurface X] in
/--
If explicit handoff skeletons over the two paths have the same terminal value,
then any globally chosen handoff skeletons over those paths give an elementary
grid move.  Same-path uniqueness removes dependence on arbitrary choices.

%%handwave
name: If explicit handoff skeletons over the two paths have the same terminal value, then any globally chosen handoff skeletons over those paths give an elementary grid move
statement:
  If explicit handoff skeletons over the two paths have the same terminal value, then any
  globally chosen handoff skeletons over those paths give an elementary grid move. Same-path
  uniqueness removes dependence on arbitrary choices.
-/
def of_terminalValueWitness
    (hSamePath :
      PathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple
        x₀ g localModels)
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels q)
    (hST : S.terminalValue = T.terminalValue) :
    PathLocalTransitionBasedWeakHandoffElementaryGridMove
      basedWeakHandoffAlong p q where
  terminalFormula_eq := by
    let Sp := basedWeakHandoffAlong p
    let Tq := basedWeakHandoffAlong q
    rw [Sp.terminalFormulaAt_endpoint, Tq.terminalFormulaAt_endpoint]
    exact (hSamePath Sp S).trans (hST.trans (hSamePath T Tq))

end PathLocalTransitionBasedWeakHandoffElementaryGridMove

/--
Value-witness form of the one-column rectangle replacement boundary.

For each chart-contained homotopy rectangle, it asks only for explicit
handoff skeletons over the two adjacent cut paths whose terminal values
agree.  A separate same-path uniqueness theorem then transfers this equality
to any globally chosen skeletons.

%%handwave
name: Value-witness form of the one-column rectangle replacement principle
statement:
  Value-witness form of the one-column rectangle replacement principle. For each chart-contained
  homotopy rectangle, it asks only for explicit handoff skeletons over the two adjacent cut
  paths whose terminal values agree. A separate same-path uniqueness theorem then transfers this
  equality to any globally chosen skeletons.
-/
def PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnValueWitnessPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (t : ℕ → unitInterval),
      t 0 = 0 →
      Monotone t →
      (i m : ℕ) →
      (∃ c : X,
        Set.Icc (t i) (t (i + 1)) ×ˢ
            Set.Icc (t m) (t (m + 1)) ⊆
          {z : unitInterval × unitInterval |
            F z ∈ (localModels.chartAt c).domain}) →
      ∃ (S :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripCutPath F (t i) (t (i + 1)) (t (m + 1))))
        (T :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripCutPath F (t i) (t (i + 1)) (t m))),
        S.terminalValue = T.terminalValue

/--
Decomposed-column value witnesses.

This is the geometric rectangle part of the one-column boundary, stated on
the path expressions with an explicit common prefix, an elementary rectangle
edge, and a common suffix.  The separate cut-reparameterization transfer below
is responsible for moving these witnesses to the public raw cut paths.

%%handwave
name: Decomposed-column value witnesses
statement:
  Decomposed-column value witnesses. This is the geometric rectangle part of the one-column
  principle, stated on the path expressions with an explicit common prefix, an elementary
  rectangle edge, and a common suffix. The separate cut-reparameterization transfer below is
  responsible for moving these witnesses to the normalized raw cut paths.
-/
def PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (t : ℕ → unitInterval),
      t 0 = 0 →
      Monotone t →
      (i m : ℕ) →
      (∃ c : X,
        Set.Icc (t i) (t (i + 1)) ×ˢ
            Set.Icc (t m) (t (m + 1)) ⊆
          {z : unitInterval × unitInterval |
            F z ∈ (localModels.chartAt c).domain}) →
      ∃ (S :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnTopPath
              F (t i) (t (i + 1)) (t m) (t (m + 1))))
        (T :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnBottomPath
              F (t i) (t (i + 1)) (t m) (t (m + 1)))),
        S.terminalValue = T.terminalValue

omit [RiemannSurface X] in
/--
The decomposed one-column value-witness principle is unconditional.

The rectangle itself is handled in one chart; the common suffix is handled by
an exact append of an arbitrary componentwise suffix skeleton, so no good-cover
or one-chart suffix assumption is needed.

%%handwave
name: A chart-contained homotopy column has matching decomposed continuation values
statement: Let $F$ be an endpoint-fixed homotopy and $(t_n)$ a monotone subdivision with $t_0=0$. If the rectangle $[t_i,t_{i+1}]\times[t_m,t_{m+1}]$ lies in one local-model chart, then there are continuation skeletons over the decomposed top and bottom column paths with equal terminal values.
proof: Continue along the common prefix, change to the chart containing the rectangle, compare its two boundary routes there, and append an arbitrary continuation skeleton along the common suffix; exact suffix extension preserves the equality.
-/
theorem pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessPrinciple_unconditional
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessPrinciple
      x₀ g localModels := by
  intro x p q F t ht0 htmono i m hRect
  rcases hRect with ⟨c, hRectc⟩
  have hab : t i ≤ t (i + 1) := htmono (Nat.le_succ i)
  have hr : t m ≤ t (m + 1) := htmono (Nat.le_succ m)
  let pref := homotopyStripColumnPrefix F (t i) (t m)
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels pref with
    ⟨S₀⟩
  have hc : F (t i, t m) ∈ (localModels.chartAt c).domain := by
    exact hRectc ⟨⟨le_rfl, hab⟩, ⟨le_rfl, hr⟩⟩
  let A :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt S₀.terminalCenter)
        (localModels.chartAt c)
        (F (t i, t m)) :=
    Classical.choice
      (localModels.transition_localRealMobius S₀.terminalCenter c
        (F (t i, t m)) ⟨S₀.terminal_endpoint_mem_domain, hc⟩)
  let S := S₀.terminalChartChangeSkeleton c hc A
  have hcenter : S.terminalCenter = c := by
    exact S₀.terminalChartChangeSkeleton_terminalCenter c hc A
  let suffix := homotopyStripColumnSuffix F (t (i + 1)) (t (m + 1))
  rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
      localModels suffix with
    ⟨C⟩
  exact
    exists_terminalValue_eq_homotopyStripColumn_suffixSkeleton
      F (t i) (t (i + 1)) (t m) (t (m + 1))
      hab hr S c hcenter hRectc C

/--
Exact transfer from decomposed column paths to the public cut paths.

The path-level homotopies
`homotopyStripColumnTopPath_homotopic_cutPathRaw` and
`homotopyStripColumnBottomPath_homotopic_cutPathRaw` show that this is only
controlled reparameterization/parenthesization of subpath concatenations,
plus the endpoint normalizations in `homotopyStripCutPath`.

%%handwave
name: Exact transfer from decomposed column paths to the normalized cut paths
statement:
  Exact transfer from decomposed column paths to the normalized cut paths. The path-level
  homotopies the homotopy from the top column path to the raw cut path and the homotopy from the
  bottom column path to the raw cut path show that this is only controlled
  reparameterization/parenthesization of subpath concatenations, plus the endpoint
  normalizations in the endpoint-normalized strip-cut path.
-/
def PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (t : ℕ → unitInterval),
      t 0 = 0 →
      Monotone t →
      (i m : ℕ) →
      (∃ c : X,
        Set.Icc (t i) (t (i + 1)) ×ˢ
            Set.Icc (t m) (t (m + 1)) ⊆
          {z : unitInterval × unitInterval |
            F z ∈ (localModels.chartAt c).domain}) →
      (∀ (S :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnTopPath
              F (t i) (t (i + 1)) (t m) (t (m + 1)))),
          ∃ (Sraw :
            PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
              (homotopyStripCutPath F (t i) (t (i + 1)) (t (m + 1)))),
            Sraw.terminalValue = S.terminalValue) ∧
        (∀ (T :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnBottomPath
              F (t i) (t (i + 1)) (t m) (t (m + 1)))),
          ∃ (Traw :
            PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
              (homotopyStripCutPath F (t i) (t (i + 1)) (t m))),
            Traw.terminalValue = T.terminalValue)

/--
Explicit witness form of the cut-reparameterization transfer.

Same-path terminal-value uniqueness removes the need to compare against every
possible skeleton over the decomposed path.  The remaining mathematical
content is just to build one decomposed skeleton and one public-cut skeleton
with the same terminal value, separately for the top and bottom edge of the
column.

%%handwave
name: Explicit witness form of the cut-reparameterization transfer
statement:
  Explicit witness form of the cut-reparameterization transfer. Same-path terminal-value
  uniqueness removes the need to compare against every possible skeleton over the decomposed
  path. The remaining mathematical content is just to build one decomposed skeleton and one
  normalized-cut skeleton with the same terminal value, separately for the top and bottom edge
  of the column.
-/
def PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (t : ℕ → unitInterval),
      t 0 = 0 →
      Monotone t →
      (i m : ℕ) →
      (∃ c : X,
        Set.Icc (t i) (t (i + 1)) ×ˢ
            Set.Icc (t m) (t (m + 1)) ⊆
          {z : unitInterval × unitInterval |
            F z ∈ (localModels.chartAt c).domain}) →
      (∃ (Scol :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnTopPath
              F (t i) (t (i + 1)) (t m) (t (m + 1))))
        (Sraw :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripCutPath F (t i) (t (i + 1)) (t (m + 1)))),
        Sraw.terminalValue = Scol.terminalValue) ∧
        (∃ (Tcol :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnBottomPath
              F (t i) (t (i + 1)) (t m) (t (m + 1))))
        (Traw :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripCutPath F (t i) (t (i + 1)) (t m))),
        Traw.terminalValue = Tcol.terminalValue)

/--
Raw-cut witness form of cut reparameterization.

This stops before the public endpoint normalizations in `homotopyStripCutPath`;
it compares decomposed column paths to `homotopyStripCutPathRaw`.  The
remaining passage from raw cut paths to public cut paths is exactly the
endpoint-normalization boundary at `r = 0` and `r = 1`.

%%handwave
name: Raw-cut witness form of cut reparameterization
statement:
  Raw-cut witness form of cut reparameterization. This stops before the normalized endpoint
  normalizations in the endpoint-normalized strip-cut path; it compares decomposed column paths
  to the raw strip-cut path. The remaining passage from raw cut paths to normalized cut paths is
  exactly the endpoint-normalization principle at r = 0 and r = 1.
-/
def PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnRawCutReparamExplicitValueWitnessPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q)
    (t : ℕ → unitInterval),
      t 0 = 0 →
      Monotone t →
      (i m : ℕ) →
      (∃ c : X,
        Set.Icc (t i) (t (i + 1)) ×ˢ
            Set.Icc (t m) (t (m + 1)) ⊆
          {z : unitInterval × unitInterval |
            F z ∈ (localModels.chartAt c).domain}) →
      (∃ (Scol :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnTopPath
              F (t i) (t (i + 1)) (t m) (t (m + 1))))
        (Sraw :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripCutPathRaw F (t i) (t (i + 1)) (t (m + 1)))),
        Sraw.terminalValue = Scol.terminalValue) ∧
        (∃ (Tcol :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripColumnBottomPath
              F (t i) (t (i + 1)) (t m) (t (m + 1))))
        (Traw :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripCutPathRaw F (t i) (t (i + 1)) (t m))),
        Traw.terminalValue = Tcol.terminalValue)

/--
Endpoint-normalization witness from raw cut paths to public cut paths.

Away from `r = 0, 1`, `homotopyStripCutPath` is definitionally the raw cut
path.  The remaining mathematical content is the two endpoint cases, where
the raw cut path contains constant endpoint pieces and the public path is
normalized to the corresponding vertical side.

%%handwave
name: Endpoint-normalization witness from raw cut paths to normalized cut paths
statement:
  Endpoint-normalization witness from raw cut paths to normalized cut paths. Away from r = 0, 1,
  the endpoint-normalized strip-cut path is definitionally the raw cut path. The remaining
  mathematical content is the two endpoint cases, where the raw cut path contains constant
  endpoint pieces and the normalized path is normalized to the corresponding vertical side.
-/
def PathLocalTransitionBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x : X} {p q : Path x₀ x}
    (F : Path.Homotopy p q) (a b r : unitInterval),
      ∃ (Sraw :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripCutPathRaw F a b r))
        (Spub :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels
            (homotopyStripCutPath F a b r)),
        Spub.terminalValue = Sraw.terminalValue

omit [RiemannSurface X] in
/--
Endpoint-normalization for strip cut paths.

At `r = 1`, the raw cut is the public lower side followed by pointwise
constant terminal pieces.  At `r = 0`, it is pointwise constant basepoint
pieces followed by the public upper side.  Away from the endpoints the public
cut is definitionally the raw cut.

%%handwave
name: Raw and normalized strip cuts have equal continuation values
statement: For every endpoint-fixed homotopy $F$ and $a,b,r\in[0,1]$, there are skeletons over the raw strip-cut path and its endpoint-normalized version whose terminal values are equal.
proof: If $r=1$, remove the constant terminal pieces by terminal extension; if $r=0$, remove the constant initial pieces by constant-prefix invariance; for $0<r<1$ the two paths are definitionally equal.
-/
theorem pathLocalTransitionBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessPrinciple_unconditional
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    PathLocalTransitionBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessPrinciple
      x₀ g localModels := by
  intro x p q F a b r
  by_cases hr1 : r = 1
  · subst r
    let γ := F.eval a
    let η := (F.evalAt (1 : unitInterval)).subpath a b
    let τ := (F.eval b).subpath (1 : unitInterval) 1
    have hη_const : ∀ t : unitInterval, η t = x := by
      intro t
      change F (Set.Icc.convexComb a b t, (1 : unitInterval)) = x
      exact F.target (Set.Icc.convexComb a b t)
    have hτ_const : ∀ t : unitInterval, τ t = x := by
      intro t
      have hτ_refl : τ = Path.refl (F (b, (1 : unitInterval))) := by
        simp [τ]
      rw [hτ_refl]
      change F (b, (1 : unitInterval)) = x
      exact F.target b
    rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
        localModels γ with
      ⟨Sγ⟩
    let Ssub := Sγ.castEndpoints γ.source γ.target
    have hηmem :
        ∀ t : unitInterval,
          η t ∈ (localModels.chartAt Ssub.terminalCenter).domain := by
      intro t
      rw [hη_const t]
      simpa [Ssub] using Sγ.terminal_endpoint_mem_domain
    let Sη := Ssub.terminalExtensionAlongSkeleton η hηmem
    have hτmem :
        ∀ t : unitInterval,
          τ t ∈ (localModels.chartAt Sη.terminalCenter).domain := by
      intro t
      have hcenter : Sη.terminalCenter = Sγ.terminalCenter := by
        rw [Ssub.terminalExtensionAlongSkeleton_terminalCenter η hηmem]
        simp [Ssub]
      rw [hτ_const t]
      rw [hcenter]
      exact Sγ.terminal_endpoint_mem_domain
    let SrawCore := Sη.terminalExtensionAlongSkeleton τ hτmem
    have hSη :
        Sη.terminalValue = Ssub.terminalValue := by
      calc
        Sη.terminalValue = Sη.terminalFormulaAt (F (b, 1)) := by
          exact Sη.terminalFormulaAt_endpoint.symm
        _ = Ssub.terminalFormulaAt (F (b, 1)) := by
          exact Ssub.terminalExtensionAlongSkeleton_terminalFormulaAt_eq η hηmem (F (b, 1))
        _ = Ssub.terminalFormulaAt (F (a, 1)) := by
          rw [F.target b, F.target a]
        _ = Ssub.terminalValue := Ssub.terminalFormulaAt_endpoint
    have hSrawCore :
        SrawCore.terminalValue = Sη.terminalValue := by
      calc
        SrawCore.terminalValue = SrawCore.terminalFormulaAt (F (b, 1)) := by
          exact SrawCore.terminalFormulaAt_endpoint.symm
        _ = Sη.terminalFormulaAt (F (b, 1)) := by
          exact Sη.terminalExtensionAlongSkeleton_terminalFormulaAt_eq τ hτmem (F (b, 1))
        _ = Sη.terminalValue := Sη.terminalFormulaAt_endpoint
    have hSsub :
        Ssub.terminalValue = Sγ.terminalValue := by
      simp [Ssub]
    let Sraw :=
      SrawCore.castEndpoints (F.source a).symm (F.target b).symm
    have hSraw :
        Sraw.terminalValue = Sγ.terminalValue := by
      rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.castEndpoints_terminalValue]
      exact hSrawCore.trans (hSη.trans hSsub)
    refine ⟨?_, ?_, ?_⟩
    · simpa [homotopyStripCutPathRaw, homotopyStripCutPathRawCore,
        γ, η, τ, Sraw, Path.subpath_zero_one] using Sraw
    · simpa [homotopyStripCutPath, γ] using Sγ
    · convert hSraw.symm <;>
        simp [homotopyStripCutPathRaw, homotopyStripCutPathRawCore,
          homotopyStripCutPath, γ, η, τ, Sraw, Path.subpath_zero_one]
  · by_cases hr0 : r = 0
    · subst r
      let δraw : Path x₀ x :=
        ((F.eval b).subpath (0 : unitInterval) 1).cast
          (F.source b).symm (F.target b).symm
      let α := (F.eval a).subpath (0 : unitInterval) 0
      let β := (F.evalAt (0 : unitInterval)).subpath a b
      let κ : Path x₀ x₀ :=
        (α.trans β).cast (F.source a).symm (F.source b).symm
      have hα_path : α = Path.refl (F (a, (0 : unitInterval))) := by
        simp [α]
      have hα_const : ∀ t : unitInterval, α t = x₀ := by
        intro t
        rw [hα_path]
        change F (a, (0 : unitInterval)) = x₀
        exact F.source a
      have hβ_const : ∀ t : unitInterval, β t = x₀ := by
        intro t
        change F (Set.Icc.convexComb a b t, (0 : unitInterval)) = x₀
        exact F.source (Set.Icc.convexComb a b t)
      have hκ : ∀ t : unitInterval, κ t = x₀ := by
        intro t
        change (α.trans β) t = x₀
        rw [Path.trans_apply]
        by_cases ht : (t : ℝ) ≤ 1 / 2
        · rw [dif_pos ht]
          exact hα_const _
        · rw [dif_neg ht]
          exact hβ_const _
      rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
          localModels δraw with
        ⟨Sδ⟩
      rcases Sδ.exists_terminalValue_eq_after_constantPrefix_trans hκ with
        ⟨Sraw₀, hraw₀⟩
      have hpub : homotopyStripCutPath F a b 0 = δraw := by
        ext t
        simp [homotopyStripCutPath, δraw, Path.subpath]
      have hrawpath : homotopyStripCutPathRaw F a b 0 = κ.trans δraw := by
        ext t
        simp [homotopyStripCutPathRaw, homotopyStripCutPathRawCore,
          δraw, β, κ, Path.cast_trans, hα_path]
        rfl
      rw [hpub, hrawpath]
      exact ⟨Sraw₀, Sδ, hraw₀.symm⟩
    · rcases exists_pathLocalTransitionModelBasedWeakHandoffSkeleton
          localModels (homotopyStripCutPathRaw F a b r) with
        ⟨S⟩
      have hpub :
          homotopyStripCutPath F a b r =
            homotopyStripCutPathRaw F a b r := by
        simp [homotopyStripCutPath, hr1, hr0]
      rw [hpub]
      exact ⟨S, S, rfl⟩

omit [RiemannSurface X] in
/--
The explicit witness form implies the arbitrary-skeleton cut-transfer form
once same-path terminal-value uniqueness is available.

%%handwave
name: One explicit cut witness transfers every decomposed continuation value
statement: Assume each chart-contained homotopy column has one top pair and one bottom pair of decomposed and public-cut skeletons with equal terminal values, and assume continuation along a fixed path has a unique terminal value. Then every decomposed top or bottom skeleton admits a public-cut skeleton with the same terminal value.
proof: Use the explicit public-cut witness on each side, then replace its paired decomposed skeleton by the arbitrary given one using fixed-path terminal-value uniqueness.
-/
theorem pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferPrinciple_of_explicitValueWitness
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hExplicit :
      PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple
        x₀ g localModels)
    (hSamePath :
      PathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferPrinciple
      x₀ g localModels := by
  intro x p q F t ht0 htmono i m hRect
  rcases hExplicit F t ht0 htmono i m hRect with
    ⟨⟨Scol, Sraw, hSraw⟩, ⟨Tcol, Traw, hTraw⟩⟩
  constructor
  · intro S
    exact ⟨Sraw, hSraw.trans (hSamePath Scol S)⟩
  · intro T
    exact ⟨Traw, hTraw.trans (hSamePath Tcol T)⟩

omit [RiemannSurface X] in
/--
Decomposed-column witnesses plus exact cut-reparameterization transfer give
the public one-column value-witness principle.

%%handwave
name: Decomposed column comparison descends to public cut paths
statement: If chart-contained columns admit equal terminal values on their decomposed top and bottom paths, and decomposed values transfer to the corresponding public cut paths, then the two public cut paths admit skeletons with equal terminal values.
proof: Choose equal-valued decomposed skeletons, transfer each to a public-cut skeleton, and compose the three terminal-value equalities.
-/
theorem pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnValueWitnessPrinciple_of_decomposed_and_cutReparam
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hDecomp :
      PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessPrinciple
        x₀ g localModels)
    (hCut :
      PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferPrinciple
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnValueWitnessPrinciple
      x₀ g localModels := by
  intro x p q F t ht0 htmono i m hRect
  rcases hDecomp F t ht0 htmono i m hRect with ⟨S, T, hST⟩
  rcases hCut F t ht0 htmono i m hRect with ⟨hTop, hBottom⟩
  rcases hTop S with ⟨Sraw, hSraw⟩
  rcases hBottom T with ⟨Traw, hTraw⟩
  exact ⟨Sraw, Traw, hSraw.trans (hST.trans hTraw.symm)⟩

omit [RiemannSurface X] in
/--
Explicit terminal-value witnesses plus same-path uniqueness prove the
one-column elementary grid-move boundary.

%%handwave
name: Equal-valued column witnesses yield an elementary grid move
statement: Fix a chosen continuation skeleton along every based path. If every chart-contained homotopy column admits explicit top and bottom cut skeletons with equal terminal values, and fixed-path terminal values are unique, then the chosen cut skeletons are connected by a one-step elementary grid walk.
proof: Transfer the explicit equality to the two chosen skeletons by fixed-path uniqueness, package the result as an elementary grid move, and regard that move as a one-step walk.
-/
theorem pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnMovePrinciple_of_valueWitness
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    (hValue :
      PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnValueWitnessPrinciple
        x₀ g localModels)
    (hSamePath :
      PathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnMovePrinciple
      x₀ g localModels basedWeakHandoffAlong := by
  intro x p q F t ht0 htmono i m hRect
  rcases hValue F t ht0 htmono i m hRect with ⟨S, T, hST⟩
  exact ⟨
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalk.ofMove
      (PathLocalTransitionBasedWeakHandoffElementaryGridMove.of_terminalValueWitness
        (basedWeakHandoffAlong := basedWeakHandoffAlong)
        hSamePath S T hST)⟩

/--
An elementary comparison move between two based weak handoff skeletons over
the same representative path.

Concrete refinement moves, subdivision insertions, and local transition
replacement moves should eventually instantiate this structure by proving
that the terminal value is preserved.
-/
structure PathLocalTransitionBasedWeakHandoffSamePathSkeletonMove
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) where
  /-- The elementary same-path move preserves the terminal value. -/
  terminalValue_eq : S.terminalValue = T.terminalValue

namespace PathLocalTransitionBasedWeakHandoffSamePathSkeletonMove

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}
    {S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}

omit [RiemannSurface X] in
/-- The terminal value equality carried by a same-path skeleton move.

%%handwave
name: A same-path comparison move preserves terminal value
statement: If $M$ is an elementary comparison move from a continuation skeleton $S$ to a skeleton $T$ over the same path, then $v(S)=v(T)$.
proof: This equality is precisely the datum carried by the comparison move.
-/
theorem terminalValue_eq_of_move
    (M :
      PathLocalTransitionBasedWeakHandoffSamePathSkeletonMove S T) :
    S.terminalValue = T.terminalValue :=
  M.terminalValue_eq

omit [RiemannSurface X] in
/--
Splitting one segment is an elementary same-path refinement move.

%%handwave
name: Splitting one segment is an elementary same-path refinement move
statement:
  Splitting one segment is an elementary same-path refinement move.
-/
noncomputable def segmentSplit
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
      PathLocalTransitionBasedWeakHandoffSamePathSkeletonMove
      S (S.segmentSplitSkeleton k τ hτ_left hτ_right) where
  terminalValue_eq := by
    simp

omit [RiemannSurface X] in
/--
Splitting at an arbitrary parameter is an elementary same-path move, with the
containing segment chosen by `exists_segment_contains_parameter`.

%%handwave
name: Splitting at an arbitrary parameter is an elementary same-path move, with the containing segment chosen by exists_segment_contains_parameter
statement:
  Splitting at an arbitrary parameter is an elementary same-path move, with the containing
  segment chosen by exists_segment_contains_parameter.
-/
noncomputable def segmentSplitAtParameter
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (τ : unitInterval) :
    PathLocalTransitionBasedWeakHandoffSamePathSkeletonMove
      S (S.splitAtParameterSkeleton τ) where
  terminalValue_eq := by
    simp

omit [RiemannSurface X] in
/--
Inserting a zero-length endpoint chart handoff is an elementary same-path move.

This is the componentwise refinement move that changes the chart used at an
existing subdivision vertex without changing the path or the terminal branch.

%%handwave
name: Inserting a zero-length endpoint chart handoff is an elementary same-path move
statement:
  Inserting a zero-length endpoint chart handoff is an elementary same-path move. This is the
  componentwise refinement move that changes the chart used at an existing subdivision vertex
  without changing the path or the terminal branch.
-/
noncomputable def segmentEndpointChartInsert
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X)
    (hc :
      p (S.parameterAt k.succ) ∈ (localModels.chartAt c).domain)
    (Tleft :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (S.centerAt k.castSucc))
        (localModels.chartAt c)
        (p (S.parameterAt k.succ)))
    (Tright :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt c)
        (localModels.chartAt (S.centerAt k.succ))
        (p (S.parameterAt k.succ))) :
      PathLocalTransitionBasedWeakHandoffSamePathSkeletonMove
      S (S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright) where
  terminalValue_eq :=
    (S.segmentEndpointChartInsertSkeleton_terminalValue_eq_of_localTransitions
      k c hc Tleft Tright).symm

end PathLocalTransitionBasedWeakHandoffSamePathSkeletonMove

/--
A finite walk of elementary same-path skeleton moves.

This is the intended combinatorial output of common-refinement arguments for
two continuation skeletons carried by the same path.
-/
structure PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) where
  /-- Number of elementary same-path moves. -/
  length : ℕ
  /-- The intermediate skeleton after `n` moves. -/
  skeletonAt :
    ℕ →
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p
  /-- The walk starts at `S`. -/
  skeletonAt_zero : skeletonAt 0 = S
  /-- The walk ends at `T`. -/
  skeletonAt_length : skeletonAt length = T
  /-- Each step is an elementary same-path skeleton move. -/
  moveAt :
    ∀ n, n < length →
      PathLocalTransitionBasedWeakHandoffSamePathSkeletonMove
        (skeletonAt n) (skeletonAt (n + 1))

namespace PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}
    {S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}

omit [RiemannSurface X] in
/-- The empty same-path skeleton move walk.

%%handwave
name: The empty same-path skeleton move walk
statement:
  The empty same-path skeleton move walk.
-/
def refl
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk S S where
  length := 0
  skeletonAt := fun _ => S
  skeletonAt_zero := rfl
  skeletonAt_length := rfl
  moveAt := by
    intro n hn
    exact False.elim ((Nat.not_lt_zero n) hn)

omit [RiemannSurface X] in
/-- A single same-path skeleton move as a finite walk.

%%handwave
name: A single same-path skeleton move as a finite walk
statement:
  A single same-path skeleton move as a finite walk.
-/
def ofMove
    (M :
      PathLocalTransitionBasedWeakHandoffSamePathSkeletonMove S T) :
    PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk S T where
  length := 1
  skeletonAt := fun n => if n = 0 then S else T
  skeletonAt_zero := by simp
  skeletonAt_length := by simp
  moveAt := by
    intro n hn
    cases n with
    | zero =>
        simpa using M
    | succ n =>
        exact False.elim
          ((Nat.not_lt_zero n) (Nat.lt_of_succ_lt_succ hn))

omit [RiemannSurface X] in
/-- Concatenate two finite same-path skeleton move walks.

%%handwave
name: Concatenate two finite same-path skeleton move walks
statement:
  Concatenate two finite same-path skeleton move walks.
-/
def trans
    {R :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    (W₁ : PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk S T)
    (W₂ : PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk T R) :
    PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk S R where
  length := W₁.length + W₂.length
  skeletonAt := fun n =>
    if h : n ≤ W₁.length then
      W₁.skeletonAt n
    else
      W₂.skeletonAt (n - W₁.length)
  skeletonAt_zero := by
    simp [W₁.skeletonAt_zero]
  skeletonAt_length := by
    by_cases hW₂zero : W₂.length = 0
    · have hTR : T = R := by
        have hlen := W₂.skeletonAt_length
        rw [hW₂zero] at hlen
        exact W₂.skeletonAt_zero.symm.trans hlen
      simp [hW₂zero, W₁.skeletonAt_length, hTR]
    · have hnot : ¬ W₁.length + W₂.length ≤ W₁.length := by
        have hpos : 0 < W₂.length := Nat.pos_of_ne_zero hW₂zero
        omega
      have hidx : W₁.length + W₂.length - W₁.length = W₂.length := by
        omega
      simp [hnot, hidx, W₂.skeletonAt_length]
  moveAt := by
    intro n hn
    by_cases hnlt : n < W₁.length
    · have hnle : n ≤ W₁.length := Nat.le_of_lt hnlt
      have hsuccle : n + 1 ≤ W₁.length := Nat.succ_le_of_lt hnlt
      simpa [hnle, hsuccle] using W₁.moveAt n hnlt
    · by_cases hn_eq : n = W₁.length
      · subst n
        have hW₂pos : 0 < W₂.length := by omega
        have hnot : ¬ W₁.length + 1 ≤ W₁.length := by omega
        have hidx : W₁.length + 1 - W₁.length = 1 := by omega
        have hidx0 : W₁.length - W₁.length = 0 := by omega
        simpa [hnot, hidx, hidx0, W₁.skeletonAt_length, W₂.skeletonAt_zero] using
          W₂.moveAt 0 hW₂pos
      · have hn_after : W₁.length < n := by omega
        have hn₂ : n - W₁.length < W₂.length := by omega
        have hnot_n : ¬ n ≤ W₁.length := by omega
        have hnot_succ : ¬ n + 1 ≤ W₁.length := by omega
        have hidx_succ : n + 1 - W₁.length = (n - W₁.length) + 1 := by
          omega
        simpa [hnot_n, hnot_succ, hidx_succ] using
          W₂.moveAt (n - W₁.length) hn₂

omit [RiemannSurface X] in
/-- Splitting one segment as a one-step same-path move walk.

%%handwave
name: Splitting one segment as a one-step same-path move walk
statement:
  Splitting one segment as a one-step same-path move walk.
-/
noncomputable def segmentSplit
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ) :
    PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk
      S (S.segmentSplitSkeleton k τ hτ_left hτ_right) :=
  ofMove
    (PathLocalTransitionBasedWeakHandoffSamePathSkeletonMove.segmentSplit
      S k τ hτ_left hτ_right)

omit [RiemannSurface X] in
/--
Splitting at an arbitrary parameter as a one-step same-path move walk.

%%handwave
name: Splitting at an arbitrary parameter as a one-step same-path move walk
statement:
  Splitting at an arbitrary parameter as a one-step same-path move walk.
-/
noncomputable def segmentSplitAtParameter
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (τ : unitInterval) :
    PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk
      S (S.splitAtParameterSkeleton τ) :=
  ofMove
    (PathLocalTransitionBasedWeakHandoffSamePathSkeletonMove.segmentSplitAtParameter
      S τ)

omit [RiemannSurface X] in
/--
Finite move walk splitting at the first `m` sampled parameters of `T`.

%%handwave
name: Finite move walk splitting at the first m sampled parameters of T
statement:
  Finite move walk splitting at the first m sampled parameters of T.
-/
noncomputable def splitFirstVerticesOf
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ m : ℕ,
      PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk
        S (S.splitFirstVerticesOfSkeleton T m)
  | 0 => PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk.refl S
  | m + 1 => by
      classical
      by_cases h : m < T.length + 1
      · let R := S.splitFirstVerticesOfSkeleton T m
        simpa [PathLocalTransitionModelBasedWeakHandoffSkeleton.splitFirstVerticesOfSkeleton,
          h, R] using
          (splitFirstVerticesOf S T m).trans
            (PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk.segmentSplitAtParameter
              R (T.parameterAt ⟨m, h⟩))
      · simpa [PathLocalTransitionModelBasedWeakHandoffSkeleton.splitFirstVerticesOfSkeleton,
          h] using splitFirstVerticesOf S T m

omit [RiemannSurface X] in
/--
Finite move walk splitting at every sampled parameter of `T`.

%%handwave
name: Finite move walk splitting at every sampled parameter of T
statement:
  Finite move walk splitting at every sampled parameter of T.
-/
noncomputable def splitAllVerticesOf
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk
      S (S.splitAllVerticesOfSkeleton T) := by
  simpa [PathLocalTransitionModelBasedWeakHandoffSkeleton.splitAllVerticesOfSkeleton]
    using splitFirstVerticesOf S T (T.length + 1)

omit [RiemannSurface X] in
/--
Endpoint chart-insertion as a one-step same-path move walk.

%%handwave
name: Endpoint chart-insertion as a one-step same-path move walk
statement:
  Endpoint chart-insertion as a one-step same-path move walk.
-/
noncomputable def segmentEndpointChartInsert
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (c : X)
    (hc :
      p (S.parameterAt k.succ) ∈ (localModels.chartAt c).domain)
    (Tleft :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (S.centerAt k.castSucc))
        (localModels.chartAt c)
        (p (S.parameterAt k.succ)))
    (Tright :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt c)
        (localModels.chartAt (S.centerAt k.succ))
        (p (S.parameterAt k.succ))) :
    PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk
      S (S.segmentEndpointChartInsertSkeleton k c hc Tleft Tright) :=
  ofMove
    (PathLocalTransitionBasedWeakHandoffSamePathSkeletonMove.segmentEndpointChartInsert
      S k c hc Tleft Tright)

omit [RiemannSurface X] in
/--
Split a segment and then insert a chosen chart at the newly-created vertex,
as a finite same-path move walk.

%%handwave
name: Split a segment and then insert a chosen chart at the newly-created vertex, as a finite same-path move walk
statement:
  Split a segment and then insert a chosen chart at the newly-created vertex, as a finite
  same-path move walk.
-/
noncomputable def segmentSplitEndpointChartInsert
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) (τ : unitInterval)
    (hτ_left : (S.parameterAt k.castSucc : ℝ) ≤ τ)
    (hτ_right : (τ : ℝ) ≤ S.parameterAt k.succ)
    (c : X)
    (hc : p τ ∈ (localModels.chartAt c).domain) :
    PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk
      S (S.segmentSplitEndpointChartInsertSkeleton
        k τ hτ_left hτ_right c hc) := by
  classical
  unfold PathLocalTransitionModelBasedWeakHandoffSkeleton.segmentSplitEndpointChartInsertSkeleton
  let R := S.segmentSplitSkeleton k τ hτ_left hτ_right
  let j : Fin R.length := k.castSucc
  have hcR :
      p (R.parameterAt j.succ) ∈ (localModels.chartAt c).domain := by
    change
      p (S.segmentSplitParameterAt k τ
          ((k.castSucc : Fin (S.length + 1)).succ)) ∈
        (localModels.chartAt c).domain
    rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.fin_castSucc_succ_eq_succ_castSucc k]
    change
      p (S.segmentSplitParameterAt k τ
          (S.segmentSplitInsertVertex k)) ∈
        (localModels.chartAt c).domain
    simpa using hc
  let Tleft :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (R.centerAt j.castSucc))
        (localModels.chartAt c)
        (p (R.parameterAt j.succ)) :=
    Classical.choice
      (localModels.transition_localRealMobius
        (R.centerAt j.castSucc) c
        (p (R.parameterAt j.succ))
        ⟨R.path_segment_mem_model_domain j (R.parameterAt j.succ)
            (R.parameterAt_mono j) le_rfl,
          hcR⟩)
  let Tright :
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt c)
        (localModels.chartAt (R.centerAt j.succ))
        (p (R.parameterAt j.succ)) :=
    Classical.choice
      (localModels.transition_localRealMobius
        c (R.centerAt j.succ)
        (p (R.parameterAt j.succ))
        ⟨hcR, R.sample_mem_model_domain j.succ⟩)
  exact
    (PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk.segmentSplit
      S k τ hτ_left hτ_right).trans
      (PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk.segmentEndpointChartInsert
        R j c hcR Tleft Tright)

omit [RiemannSurface X] in
/--
Split at an arbitrary parameter and insert a chosen chart there, as a finite
same-path move walk.

%%handwave
name: Split at an arbitrary parameter and insert a chosen chart there, as a finite same-path move walk
statement:
  Split at an arbitrary parameter and insert a chosen chart there, as a finite same-path move
  walk.
-/
noncomputable def splitAtParameterEndpointChartInsert
    (S :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (τ : unitInterval) (c : X)
    (hc : p τ ∈ (localModels.chartAt c).domain) :
    PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk
      S (S.splitAtParameterEndpointChartInsertSkeleton τ c hc) := by
  classical
  unfold PathLocalTransitionModelBasedWeakHandoffSkeleton.splitAtParameterEndpointChartInsertSkeleton
  exact
    PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk.segmentSplitEndpointChartInsert
      S
      (Classical.choose (S.exists_segment_contains_parameter τ))
      τ
      (Classical.choose_spec (S.exists_segment_contains_parameter τ)).1
      (Classical.choose_spec (S.exists_segment_contains_parameter τ)).2
      c hc

omit [RiemannSurface X] in
/--
Finite move walk inserting the first `m` sampled vertices of `T` into `S`.

%%handwave
name: Finite move walk inserting the first m sampled vertices of T into S
statement:
  Finite move walk inserting the first m sampled vertices of T into S.
-/
noncomputable def insertFirstVerticesOf
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ∀ m : ℕ,
      PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk
        S (S.insertFirstVerticesOfSkeleton T m)
  | 0 => PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk.refl S
  | m + 1 => by
      classical
      by_cases h : m < T.length + 1
      · let R := S.insertFirstVerticesOfSkeleton T m
        have hc :
            p (T.parameterAt ⟨m, h⟩) ∈
              (localModels.chartAt (T.centerAt ⟨m, h⟩)).domain := by
          simpa using T.sample_mem_model_domain ⟨m, h⟩
        simpa [PathLocalTransitionModelBasedWeakHandoffSkeleton.insertFirstVerticesOfSkeleton,
          h, R] using
          (insertFirstVerticesOf S T m).trans
            (PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk.splitAtParameterEndpointChartInsert
              R (T.parameterAt ⟨m, h⟩) (T.centerAt ⟨m, h⟩) hc)
      · simpa [PathLocalTransitionModelBasedWeakHandoffSkeleton.insertFirstVerticesOfSkeleton,
          h] using insertFirstVerticesOf S T m

omit [RiemannSurface X] in
/--
Finite move walk inserting every sampled vertex of `T` into `S`.

%%handwave
name: Finite move walk inserting every sampled vertex of T into S
statement:
  Finite move walk inserting every sampled vertex of T into S.
-/
noncomputable def insertAllVerticesOf
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk
      S (S.insertAllVerticesOfSkeleton T) := by
  simpa [PathLocalTransitionModelBasedWeakHandoffSkeleton.insertAllVerticesOfSkeleton]
    using insertFirstVerticesOf S T (T.length + 1)

omit [RiemannSurface X] in
/-- A finite same-path skeleton move walk preserves terminal value.

%%handwave
name: A finite same-path move walk preserves terminal value
statement: If $S=S_0,S_1,\ldots,S_N=T$ is a finite walk of terminal-value-preserving comparison moves, then $v(S)=v(T)$.
proof: Induct along the walk, composing the equality supplied by each move; identify the zeroth and final skeletons with $S$ and $T$.
-/
theorem terminalValue_start_eq_end
    (W :
      PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk S T) :
    S.terminalValue = T.terminalValue := by
  have hprefix :
      ∀ m, m ≤ W.length →
        (W.skeletonAt 0).terminalValue = (W.skeletonAt m).terminalValue := by
    intro m hm
    induction m with
    | zero =>
        rfl
    | succ m ih =>
        have hm_lt : m < W.length := Nat.lt_of_succ_le hm
        exact (ih (Nat.le_of_lt hm_lt)).trans
          ((W.moveAt m hm_lt).terminalValue_eq_of_move)
  have h := hprefix W.length le_rfl
  rw [W.skeletonAt_zero, W.skeletonAt_length] at h
  exact h

end PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk



/--
Mutual vertex-refinement terminal-value comparison.

This is a sharper one-dimensional boundary than arbitrary same-path
uniqueness: before comparing two handoff skeletons, insert all sampled
vertices of each skeleton into the other.

%%handwave
name: Mutual vertex-refinement terminal-value comparison
statement:
  Mutual vertex-refinement terminal-value comparison. This is a sharper one-dimensional
  principle than arbitrary same-path uniqueness: before comparing two handoff skeletons, insert
  all sampled vertices of each skeleton into the other.
-/
def PathLocalTransitionBasedWeakHandoffMutualVertexRefinementTerminalValuePrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x : X} {p : Path x₀ x}
    (S T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p),
      (S.insertAllVerticesOfSkeleton T).terminalValue =
        (T.insertAllVerticesOfSkeleton S).terminalValue

/--
Mutual vertex-refinement common aligned-subdivision comparison.

This is the purely combinatorial/topological part of the mutual-refinement
boundary: after inserting all sampled vertices of each skeleton into the
other, allow terminal-value-preserving same-path moves to a pair of refinements
with the same subdivision parameters.  The local PSL branch comparison for
that aligned pair is then supplied by the componentwise transition atlas.

%%handwave
name: Mutual vertex-refinement common aligned-subdivision comparison
statement:
  Mutual vertex-refinement common aligned-subdivision comparison. This is the purely
  combinatorial/topological part of the mutual-refinement principle: after inserting all sampled
  vertices of each skeleton into the other, allow terminal-value-preserving same-path moves to a
  pair of refinements with the same subdivision parameters. The local PSL branch comparison for
  that aligned pair is then supplied by the componentwise transition atlas.
-/
def PathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x : X} {p : Path x₀ x}
    (S T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p),
      ∃ (U V :
          PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p),
      Nonempty
        (PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk
          (S.insertAllVerticesOfSkeleton T) U) ∧
      Nonempty
        (PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk
          (T.insertAllVerticesOfSkeleton S) V) ∧
      ∃ _hLength :
        U.length = V.length,
        ∀ n
          (hnU : n ≤ U.length)
          (hnV : n ≤ V.length),
          U.parameterAt ⟨n, Nat.lt_succ_of_le hnU⟩ =
            V.parameterAt ⟨n, Nat.lt_succ_of_le hnV⟩

omit [RiemannSurface X] in
/--
The deterministic own-split parameter-alignment boundary.

After mutual endpoint-chart insertion, the left refinement has one original
copy of each `S` vertex and two inserted copies of each `T` vertex; the right
refinement has the opposite multiplicities.  Splitting the left side at all
original `S` vertices and the right side at all original `T` vertices makes
the lengths equal automatically.  The only remaining content is that these
two weakly ordered finite parameter lists agree pointwise.

%%handwave
name: The deterministic own-split parameter-alignment principle
statement:
  The deterministic own-split parameter-alignment principle. After mutual endpoint-chart
  insertion, the left refinement has one original copy of each S vertex and two inserted copies
  of each T vertex; the right refinement has the opposite multiplicities. Splitting the left
  side at all original S vertices and the right side at all original T vertices makes the
  lengths equal automatically. The only remaining content is that these two weakly ordered
  finite parameter lists agree pointwise.
-/
def PathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x : X} {p : Path x₀ x}
    (S T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p),
      let U := (S.insertAllVerticesOfSkeleton T).splitAllVerticesOfSkeleton S
      let V := (T.insertAllVerticesOfSkeleton S).splitAllVerticesOfSkeleton T
      ∀ n
        (hnU : n ≤ U.length)
        (hnV : n ≤ V.length),
        U.parameterAt ⟨n, Nat.lt_succ_of_le hnU⟩ =
          V.parameterAt ⟨n, Nat.lt_succ_of_le hnV⟩

omit [RiemannSurface X] in
/--
The multiset/permutation form of the own-split alignment boundary.

Since every skeleton parameter list is weakly sorted, a permutation of the two
own-split parameter lists is enough to recover pointwise alignment.

%%handwave
name: The multiset/permutation form of the own-split alignment principle
statement:
  The multiset/permutation form of the own-split alignment principle. Since every skeleton
  parameter list is weakly sorted, a permutation of the two own-split parameter lists is enough
  to recover pointwise alignment.
-/
def PathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationPrinciple
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g) :
    Prop :=
  ∀ {x : X} {p : Path x₀ x}
    (S T : PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p),
      let U := (S.insertAllVerticesOfSkeleton T).splitAllVerticesOfSkeleton S
      let V := (T.insertAllVerticesOfSkeleton S).splitAllVerticesOfSkeleton T
      List.Perm U.parameterList V.parameterList

omit [RiemannSurface X] in
/--
The deterministic own-split parameter-permutation boundary is finite
bookkeeping: mutual endpoint-chart insertion contributes two copies of the
other subdivision's parameters, and the final own-split contributes the
missing second copy of the original subdivision.

%%handwave
name: The two mutual vertex refinements have the same parameter multiset
statement: For skeletons $S,T$ over the same path, let $U$ be obtained by inserting every vertex of $T$ into $S$ and then splitting at every vertex of $S$, and define $V$ symmetrically. Then the finite parameter lists of $U$ and $V$ are permutations of one another.
proof: Insertion gives two copies of the other skeleton’s parameter list and the final split supplies the second copy of the original list. Rearranging concatenations shows both lists are permutations of two copies of each original parameter list.
-/
theorem pathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationPrinciple
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g} :
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationPrinciple
      x₀ g localModels := by
  intro x p S T
  let S' := S.insertAllVerticesOfSkeleton T
  let T' := T.insertAllVerticesOfSkeleton S
  let U := S'.splitAllVerticesOfSkeleton S
  let V := T'.splitAllVerticesOfSkeleton T
  change List.Perm U.parameterList V.parameterList
  have hUSplit :
      List.Perm U.parameterList (S.parameterList ++ S'.parameterList) := by
    simpa [U, S'] using S'.splitAllVerticesOfSkeleton_parameterList_perm S
  have hSInsert :
      List.Perm S'.parameterList
        ((T.parameterList ++ T.parameterList) ++ S.parameterList) := by
    simpa [S'] using S.insertAllVerticesOfSkeleton_parameterList_perm T
  have hU :
      List.Perm U.parameterList
        (S.parameterList ++
          ((T.parameterList ++ T.parameterList) ++ S.parameterList)) :=
    hUSplit.trans (List.Perm.append_left S.parameterList hSInsert)
  have hVSplit :
      List.Perm V.parameterList (T.parameterList ++ T'.parameterList) := by
    simpa [V, T'] using T'.splitAllVerticesOfSkeleton_parameterList_perm T
  have hTInsert :
      List.Perm T'.parameterList
        ((S.parameterList ++ S.parameterList) ++ T.parameterList) := by
    simpa [T'] using T.insertAllVerticesOfSkeleton_parameterList_perm S
  have hV :
      List.Perm V.parameterList
        (T.parameterList ++
          ((S.parameterList ++ S.parameterList) ++ T.parameterList)) :=
    hVSplit.trans (List.Perm.append_left T.parameterList hTInsert)
  let A := S.parameterList
  let B := T.parameterList
  have hLeftNorm :
      List.Perm (A ++ ((B ++ B) ++ A)) ((A ++ A) ++ (B ++ B)) := by
    have hmove :
        List.Perm (((B ++ B) ++ A)) (A ++ (B ++ B)) :=
      (List.perm_append_comm :
        List.Perm ((B ++ B) ++ A) (A ++ (B ++ B)))
    have h := List.Perm.append_left A hmove
    simpa [List.append_assoc] using h
  have hRightNorm :
      List.Perm (B ++ ((A ++ A) ++ B)) ((A ++ A) ++ (B ++ B)) := by
    have hmove :
        List.Perm (B ++ (A ++ A)) ((A ++ A) ++ B) :=
      (List.perm_append_comm :
        List.Perm (B ++ (A ++ A)) ((A ++ A) ++ B))
    have h := List.Perm.append_right B hmove
    simpa [List.append_assoc] using h
  have hMiddle :
      List.Perm
        (S.parameterList ++
          ((T.parameterList ++ T.parameterList) ++ S.parameterList))
        (T.parameterList ++
          ((S.parameterList ++ S.parameterList) ++ T.parameterList)) := by
    simpa [A, B] using hLeftNorm.trans hRightNorm.symm
  exact hU.trans (hMiddle.trans hV.symm)

omit [RiemannSurface X] in
/--
The own-split padding on the two mutual vertex refinements has equal length.

%%handwave
name: The two padded mutual vertex refinements have equal length
statement: For skeletons $S,T$ over the same path, the refinement obtained from $S$ by inserting all vertices of $T$ and then splitting at all vertices of $S$ has the same length as the symmetric refinement obtained from $T$.
proof: Expand the two lengths as $|S|+2(|T|+1)+(|S|+1)$ and $|T|+2(|S|+1)+(|T|+1)$ and simplify the natural-number identity.
-/
theorem mutualVertexRefinementOwnSplit_length_eq
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}
    (S T :
      PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p) :
    ((S.insertAllVerticesOfSkeleton T).splitAllVerticesOfSkeleton S).length =
      ((T.insertAllVerticesOfSkeleton S).splitAllVerticesOfSkeleton T).length := by
  have hU :
      ((S.insertAllVerticesOfSkeleton T).splitAllVerticesOfSkeleton S).length =
        S.length + 2 * (T.length + 1) + (S.length + 1) := by
    simp [Nat.add_assoc]
  have hV :
      ((T.insertAllVerticesOfSkeleton S).splitAllVerticesOfSkeleton T).length =
        T.length + 2 * (S.length + 1) + (T.length + 1) := by
    simp [Nat.add_assoc]
  rw [hU, hV]
  omega

omit [RiemannSurface X] in
/--
The permutation form of the own-split boundary implies pointwise own-split
parameter alignment by sorted-list uniqueness.

%%handwave
name: Sorted parameter permutations are pointwise aligned
statement: If the two padded mutual vertex refinements of every pair $S,T$ have permuted parameter lists, then their parameters agree at every index valid on both sides.
proof: Both parameter lists are weakly increasing. Sorted lists that are permutations are equal, so equality of their optional entries at index $n$ gives equality of the two subdivision parameters.
-/
theorem pathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentPrinciple_of_parameterPermutation
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hPerm :
      PathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationPrinciple
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentPrinciple
      x₀ g localModels := by
  intro x p S T
  let U := (S.insertAllVerticesOfSkeleton T).splitAllVerticesOfSkeleton S
  let V := (T.insertAllVerticesOfSkeleton S).splitAllVerticesOfSkeleton T
  change ∀ n
      (hnU : n ≤ U.length)
      (hnV : n ≤ V.length),
      U.parameterAt ⟨n, Nat.lt_succ_of_le hnU⟩ =
        V.parameterAt ⟨n, Nat.lt_succ_of_le hnV⟩
  intro n hnU hnV
  have hList : U.parameterList = V.parameterList :=
    List.Perm.eq_of_sortedLE U.parameterList_sortedLE V.parameterList_sortedLE
      (hPerm S T)
  have hget := congrArg (fun l : List unitInterval => l[n]?) hList
  change U.parameterList[n]? = V.parameterList[n]? at hget
  have hUget :
      U.parameterList[n]? =
        some (U.parameterAt ⟨n, Nat.lt_succ_of_le hnU⟩) := by
    rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.parameterList,
      List.getElem?_ofFn]
    simp [Nat.lt_succ_of_le hnU]
  have hVget :
      V.parameterList[n]? =
        some (V.parameterAt ⟨n, Nat.lt_succ_of_le hnV⟩) := by
    rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.parameterList,
      List.getElem?_ofFn]
    simp [Nat.lt_succ_of_le hnV]
  rw [hUget, hVget] at hget
  exact Option.some.inj hget

omit [RiemannSurface X] in
/--
The own-split parameter-alignment boundary is unconditional.

%%handwave
name: The padded mutual vertex refinements are pointwise aligned
statement: For every pair of continuation skeletons $S,T$ over one path, their mutually inserted and own-split refinements have equal parameters at every common index.
proof: Apply sorted-list uniqueness to [the two refinements have permuted parameter lists](lean:JJMath.HyperbolicMetric.pathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationPrinciple).
-/
theorem pathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentPrinciple_unconditional
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g} :
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentPrinciple
      x₀ g localModels :=
  pathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentPrinciple_of_parameterPermutation
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationPrinciple

omit [RiemannSurface X] in
/--
The own-split parameter-alignment boundary implies the more flexible common
aligned-subdivision boundary by taking the own-split refinements as the
common aligned pair.

%%handwave
name: Own-split alignment produces common aligned mutual refinements
statement: If the canonical padded mutual refinements of $S,T$ are pointwise parameter-aligned, then the two mutual vertex insertions admit further same-path refinements $U,V$ of equal length with identical parameter at every index.
proof: Take $U,V$ to be the canonical own-split refinements. Splitting supplies the two refinement walks, their lengths agree by arithmetic, and the assumed alignment supplies pointwise equality.
-/
theorem pathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple_of_ownSplitParameterAlignment
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAlign :
      PathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentPrinciple
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple
      x₀ g localModels := by
  intro x p S T
  let S' := S.insertAllVerticesOfSkeleton T
  let T' := T.insertAllVerticesOfSkeleton S
  let U := S'.splitAllVerticesOfSkeleton S
  let V := T'.splitAllVerticesOfSkeleton T
  refine ⟨U, V, ?_, ?_, ?_, ?_⟩
  · exact
      ⟨PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk.splitAllVerticesOf
        S' S⟩
  · exact
      ⟨PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk.splitAllVerticesOf
        T' T⟩
  · exact mutualVertexRefinementOwnSplit_length_eq S T
  · intro n hnU hnV
    exact hAlign S T n hnU hnV

omit [RiemannSurface X] in
/--
The common aligned-subdivision mutual-refinement boundary is unconditional.

%%handwave
name: Mutual vertex insertions admit common aligned subdivisions
statement: For every pair of skeletons $S,T$ over the same path, the two mutual vertex insertions admit terminal-value-preserving refinements $U,V$ of equal length whose subdivision parameters agree pointwise.
proof: Use the canonical padded mutual refinements and [their unconditional pointwise alignment](lean:JJMath.HyperbolicMetric.pathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentPrinciple_unconditional).
-/
theorem pathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple_unconditional
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g} :
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple
      x₀ g localModels :=
  pathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple_of_ownSplitParameterAlignment
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentPrinciple_unconditional

/--
Aligned mutual vertex refinements give mutual-refinement terminal-value
comparison.  The proof is the aligned-subdivision branch comparison above,
with vertexwise local transitions supplied by the local-transition atlas.

%%handwave
name: Aligned mutual refinements have equal terminal values
statement: Suppose the mutual vertex insertions of every pair $S,T$ admit equal-length, pointwise parameter-aligned refinements. Then the terminal value after inserting all vertices of $T$ into $S$ equals the terminal value after inserting all vertices of $S$ into $T$.
proof: Choose a local transition between the two charts at every aligned subdivision vertex. The aligned-subdivision comparison identifies the refined terminal values, and the refinement walks transport that equality back to the two mutual insertions.
-/
theorem pathLocalTransitionBasedWeakHandoffMutualVertexRefinementTerminalValuePrinciple_of_mutualVertexRefinementCommonAlignedSubdivision
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAlign :
      PathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementTerminalValuePrinciple
      x₀ g localModels := by
  classical
  intro x p S T
  let S' := S.insertAllVerticesOfSkeleton T
  let T' := T.insertAllVerticesOfSkeleton S
  rcases hAlign S T with
    ⟨U, V, ⟨walkS⟩, ⟨walkT⟩, hLength, hParam⟩
  let Avertex :
      ∀ n (hnU : n ≤ U.length) (hnV : n ≤ V.length),
        HyperbolicLocalChart.LocalRealMobiusTransitionData
          (localModels.chartAt
            (U.centerAt ⟨n, Nat.lt_succ_of_le hnU⟩))
          (localModels.chartAt
            (V.centerAt ⟨n, Nat.lt_succ_of_le hnV⟩))
          (p (U.parameterAt ⟨n, Nat.lt_succ_of_le hnU⟩)) := by
    intro n hnU hnV
    refine Classical.choice
      (localModels.transition_localRealMobius
        (U.centerAt ⟨n, Nat.lt_succ_of_le hnU⟩)
        (V.centerAt ⟨n, Nat.lt_succ_of_le hnV⟩)
        (p (U.parameterAt ⟨n, Nat.lt_succ_of_le hnU⟩))
        ?_)
    constructor
    · exact U.sample_mem_model_domain ⟨n, Nat.lt_succ_of_le hnU⟩
    · have hTmem :
          p (V.parameterAt ⟨n, Nat.lt_succ_of_le hnV⟩) ∈
            (localModels.chartAt
              (V.centerAt ⟨n, Nat.lt_succ_of_le hnV⟩)).domain :=
        V.sample_mem_model_domain ⟨n, Nat.lt_succ_of_le hnV⟩
      simpa [hParam n hnU hnV] using hTmem
  have hUV : U.terminalValue = V.terminalValue :=
    U.terminalValue_eq_of_alignedSubdivision V hLength hParam Avertex
  calc
    S'.terminalValue = U.terminalValue := walkS.terminalValue_start_eq_end
    _ = V.terminalValue := hUV
    _ = T'.terminalValue := walkT.terminalValue_start_eq_end.symm

/--
The mutual vertex-refinement terminal-value comparison is unconditional.

%%handwave
name: Mutual vertex insertion preserves a common terminal value
statement: For any skeletons $S,T$ over the same path, inserting every vertex of $T$ into $S$ and inserting every vertex of $S$ into $T$ produce skeletons with equal terminal values.
proof: Apply the aligned-subdivision comparison to [the unconditional common aligned mutual refinements](lean:JJMath.HyperbolicMetric.pathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple_unconditional).
-/
theorem pathLocalTransitionBasedWeakHandoffMutualVertexRefinementTerminalValuePrinciple_unconditional
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g} :
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementTerminalValuePrinciple
      x₀ g localModels :=
  pathLocalTransitionBasedWeakHandoffMutualVertexRefinementTerminalValuePrinciple_of_mutualVertexRefinementCommonAlignedSubdivision
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple_unconditional

/--
Mutual vertex-refinement comparison implies same-path terminal-value
uniqueness, because finite vertex insertion preserves terminal values on both
sides.

%%handwave
name: Equal mutual refinements imply terminal-value uniqueness
statement: Assume that the two mutual vertex insertions of any same-path skeletons $S,T$ have equal terminal values. Then $v(S)=v(T)$.
proof: Insert all vertices of $T$ into $S$ and conversely. The insertion walks preserve the two original values, and the assumed equality identifies the inserted values.
-/
theorem pathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple_of_mutualVertexRefinementTerminalValue
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMutual :
      PathLocalTransitionBasedWeakHandoffMutualVertexRefinementTerminalValuePrinciple
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple
      x₀ g localModels := by
  intro x p S T
  have hS :
      S.terminalValue = (S.insertAllVerticesOfSkeleton T).terminalValue :=
    (PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk.insertAllVerticesOf
      S T).terminalValue_start_eq_end
  have hT :
      T.terminalValue = (T.insertAllVerticesOfSkeleton S).terminalValue :=
    (PathLocalTransitionBasedWeakHandoffSamePathSkeletonMoveWalk.insertAllVerticesOf
      T S).terminalValue_start_eq_end
  exact hS.trans ((hMutual S T).trans hT.symm)

/--
%%handwave
name:
  Independence of the continuation subdivision
statement:
  Fix a path $p:[0,1]\to X$ starting at $x_0$. Any two finite continuation
  chains for the same normalized local hyperbolic branch along $p$ have the
  same terminal value in $\mathbb H$.
proof:
  Insert every subdivision vertex and every selected chart of either chain
  into the other, then split both refinements to a common ordered subdivision.
  The transition cocycle identifies the aligned accumulated branches, while
  each insertion and split preserves the terminal value.
-/
theorem pathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple_unconditional
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g} :
    PathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple
      x₀ g localModels :=
  pathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple_of_mutualVertexRefinementTerminalValue
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementTerminalValuePrinciple_unconditional

/--
With same-path terminal-value uniqueness discharged, the public
cut-transfer boundary is exactly the sharper explicit witness boundary.

%%handwave
name: Explicit cut witnesses transfer arbitrary decomposed values
statement: If every chart-contained homotopy column has one equal-valued decomposed/public-cut skeleton pair on each horizontal side, then every decomposed skeleton on either side admits an equal-valued public-cut skeleton.
proof: Apply the explicit-witness transfer theorem and use unconditional uniqueness of the terminal value along a fixed path.
-/
theorem pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferPrinciple_of_explicitValueWitness_unconditional
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hExplicit :
      PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferPrinciple
      x₀ g localModels :=
  pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferPrinciple_of_explicitValueWitness
    hExplicit
    pathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple_unconditional

/--
The raw-cut reparameterization witness follows from the monotone
one-dimensional subpath-merge boundaries.

This is the mathematically sharp route for the grid proof: the only subpaths
merged here are adjacent pieces of the monotone subdivision `t`.

%%handwave
name: Monotone subpath merging supplies raw cut witnesses
statement: Assume continuation data are invariant under merging adjacent monotone subpaths, both initially and after a prefix. For every monotone grid subdivision, each chart-contained column admits equal-valued skeleton pairs comparing its decomposed top and bottom routes with the corresponding raw cut paths.
proof: Monotonicity gives the required order of the two vertical cut parameters. Apply the monotone unprefixed and prefixed merge comparisons, then transport their equalities through endpoint casts.
-/
theorem pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnRawCutReparamExplicitValueWitnessPrinciple_of_monotoneSubpathMerge
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMerge :
      PathLocalTransitionBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessPrinciple
        g localModels)
    (hPrefMerge :
      PathLocalTransitionBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessPrinciple
        g localModels) :
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnRawCutReparamExplicitValueWitnessPrinciple
      x₀ g localModels := by
  intro x p q F t ht0 htmono i m hRect
  let a := t i
  let b := t (i + 1)
  let r₀ := t m
  let r₁ := t (m + 1)
  have hr : r₀ ≤ r₁ := htmono (Nat.le_succ m)
  have hSameAtSource :
      ∀ {y : X} {path : Path (F (a, 0)) y}
        (S T :
          PathLocalTransitionModelBasedWeakHandoffSkeleton
            (F (a, 0)) g localModels path),
        S.terminalValue = T.terminalValue := by
    intro y path S T
    exact
      pathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple_unconditional
        S T
  rcases
    exists_terminalValue_eq_homotopyStripColumnTop_rawCutPathRawCore_of_monotoneSubpathMerge
      F a b r₀ r₁ hr hMerge hSameAtSource with
    ⟨ScolTopCore, SrawTopCore, hTopCore⟩
  rcases
    exists_terminalValue_eq_homotopyStripColumnBottom_rawCutPathRawCore_of_monotonePrefixedSubpathMerge
      F a b r₀ r₁ hr hPrefMerge hSameAtSource with
    ⟨ScolBottomCore, SrawBottomCore, hBottomCore⟩
  have hsource : x₀ = F (a, 0) := by
    exact (F.source a).symm
  have htarget : x = F (b, 1) := by
    exact (F.target b).symm
  let ScolTopCast :=
    ScolTopCore.castEndpoints hsource htarget
  let SrawTopCast :=
    SrawTopCore.castEndpoints hsource htarget
  let ScolBottomCast :=
    ScolBottomCore.castEndpoints hsource htarget
  let SrawBottomCast :=
    SrawBottomCore.castEndpoints hsource htarget
  have hTopCast :
      SrawTopCast.terminalValue = ScolTopCast.terminalValue := by
    rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.castEndpoints_terminalValue,
      PathLocalTransitionModelBasedWeakHandoffSkeleton.castEndpoints_terminalValue]
    exact hTopCore
  have hBottomCast :
      SrawBottomCast.terminalValue = ScolBottomCast.terminalValue := by
    rw [PathLocalTransitionModelBasedWeakHandoffSkeleton.castEndpoints_terminalValue,
      PathLocalTransitionModelBasedWeakHandoffSkeleton.castEndpoints_terminalValue]
    exact hBottomCore
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · simpa [a, b, r₀, r₁, homotopyStripColumnTopPath] using ScolTopCast
    · simpa [a, b, r₀, r₁, homotopyStripCutPathRaw] using SrawTopCast
    · simpa using hTopCast
  · refine ⟨?_, ?_, ?_⟩
    · simpa [a, b, r₀, r₁, homotopyStripColumnBottomPath] using ScolBottomCast
    · simpa [a, b, r₀, r₁, homotopyStripCutPathRaw] using SrawBottomCast
    · simpa using hBottomCast

omit [RiemannSurface X] in
/--
Raw-cut witnesses plus endpoint normalization give public cut witnesses.

%%handwave
name: Raw witnesses and endpoint normalization give public cut witnesses
statement: If decomposed column paths admit equal-valued raw-cut skeletons, raw and normalized cut paths admit equal-valued skeletons, and fixed-path terminal values are unique, then decomposed paths admit equal-valued public-cut skeletons on both sides of every chart-contained column.
proof: Normalize the top and bottom raw cuts. On each side, use fixed-path uniqueness to identify the raw skeleton chosen by normalization with the raw skeleton supplied by the column witness, then compose equalities.
-/
theorem pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple_of_rawCut_and_endpointNormalization
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hRaw :
      PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnRawCutReparamExplicitValueWitnessPrinciple
        x₀ g localModels)
    (hNormalize :
      PathLocalTransitionBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessPrinciple
        x₀ g localModels)
    (hSamePath :
      PathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple
      x₀ g localModels := by
  intro x p q F t ht0 htmono i m hRect
  rcases hRaw F t ht0 htmono i m hRect with
    ⟨⟨Scol, Sraw, hTopRaw⟩, ⟨Tcol, Traw, hBottomRaw⟩⟩
  rcases hNormalize F (t i) (t (i + 1)) (t (m + 1)) with
    ⟨Sraw₀, Spub, hTopNorm⟩
  rcases hNormalize F (t i) (t (i + 1)) (t m) with
    ⟨Traw₀, Tpub, hBottomNorm⟩
  constructor
  · refine ⟨Scol, Spub, ?_⟩
    exact hTopNorm.trans ((hSamePath Sraw₀ Sraw).trans hTopRaw)
  · refine ⟨Tcol, Tpub, ?_⟩
    exact hBottomNorm.trans ((hSamePath Traw₀ Traw).trans hBottomRaw)

/-- Raw-cut witnesses and endpoint normalization give public cut witnesses once fixed-path terminal values are known to be unique.

%%handwave
name: Raw witnesses and endpoint normalization suffice for public cut witnesses
statement: If every chart-contained column admits equal-valued decomposed/raw-cut skeleton pairs and every raw cut admits an equal-valued normalized-cut skeleton, then every column admits equal-valued decomposed/public-cut pairs.
proof: Apply the raw-to-public transfer and discharge fixed-path terminal-value uniqueness by the unconditional subdivision-independence theorem.
-/
theorem pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple_of_rawCut_and_endpointNormalization_unconditional
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hRaw :
      PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnRawCutReparamExplicitValueWitnessPrinciple
        x₀ g localModels)
    (hNormalize :
      PathLocalTransitionBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessPrinciple
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple
      x₀ g localModels :=
  pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple_of_rawCut_and_endpointNormalization
    hRaw hNormalize
    pathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple_unconditional

/--
Monotone subpath merge, monotone prefixed subpath merge, and endpoint
normalization together give the public explicit cut-reparameterization
witness.

%%handwave
name: Monotone merging and endpoint normalization give public cut witnesses
statement: If monotone subpath merging preserves continuation data both initially and after a prefix, and raw strip cuts can be normalized without changing terminal value, then every chart-contained homotopy column admits equal-valued decomposed/public-cut skeleton pairs on its top and bottom sides.
proof: First obtain decomposed/raw-cut witnesses from monotone subpath merging, then pass from raw cuts to public cuts using endpoint normalization and fixed-path uniqueness.
-/
theorem pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple_of_monotoneSubpathMerge_and_endpointNormalization
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMerge :
      PathLocalTransitionBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessPrinciple
        g localModels)
    (hPrefMerge :
      PathLocalTransitionBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessPrinciple
        g localModels)
    (hNormalize :
      PathLocalTransitionBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessPrinciple
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple
      x₀ g localModels :=
  pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple_of_rawCut_and_endpointNormalization_unconditional
    (pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnRawCutReparamExplicitValueWitnessPrinciple_of_monotoneSubpathMerge
      hMerge hPrefMerge)
    hNormalize

/--
After same-path uniqueness is discharged, the one-column boundary is exactly
the explicit terminal-value witness boundary.

%%handwave
name: Column value witnesses determine the chosen elementary grid moves
statement: Fix one continuation skeleton along each based path. If every chart-contained homotopy column admits top and bottom cut skeletons with equal terminal values, then the chosen cut skeletons are joined by an elementary grid-move walk.
proof: Use unconditional same-path terminal-value uniqueness to transfer the explicit equality to the chosen skeletons, then package it as a one-step grid walk.
-/
theorem pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnMovePrinciple_of_valueWitness_unconditional
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    (hValue :
      PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnValueWitnessPrinciple
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnMovePrinciple
      x₀ g localModels basedWeakHandoffAlong :=
  pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnMovePrinciple_of_valueWitness
    hValue
    pathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple_unconditional

/--
Same-path terminal-value uniqueness upgrades explicit existential
terminal-sheet extension to local-extension compatibility for any chosen
based weak handoff skeletons.

%%handwave
name: Fixed-path uniqueness makes chosen continuation compatible with terminal sheets
statement: Fix a continuation skeleton $S(p)$ along every based path. If all skeletons over a fixed path have the same terminal value, then for every $y$ in the terminal sheet of $S(p)$, appending the sheet path gives $F_{S(pstar y)}(π(y))=F_{S(p)}(π(y))$.
proof: Choose an explicit value-preserving terminal extension $T$. Fixed-path uniqueness identifies $T$ with the globally chosen skeleton on the appended path, and the explicit extension identifies its endpoint formula with that of $S(p)$.
-/
theorem pathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple_of_samePathTerminalValueUniqueness
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p}
    (hUnique :
      PathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple
        x₀ g localModels) :
    PathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple
      x₀ g localModels basedWeakHandoffAlong := by
  intro x p y' hy'
  let S := basedWeakHandoffAlong p
  let q := p.trans (S.terminalSheetPathInSet hy')
  rcases pathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionExistencePrinciple
      x₀ g localModels S hy' with
    ⟨T, hT⟩
  let U := basedWeakHandoffAlong q
  calc
    U.terminalFormulaAt (PathHomotopyUniversalCover.endpoint y') =
        U.terminalValue := rfl
    _ = T.terminalValue := (hUnique T U).symm
    _ = T.terminalFormulaAt (PathHomotopyUniversalCover.endpoint y') := rfl
    _ = S.terminalFormulaAt (PathHomotopyUniversalCover.endpoint y') := hT

/--
Homotopy-grid walks plus local extension inside the terminal sheet prove the
terminal-sheet homotopy principle.

%%handwave
name: Grid homotopy and local extension give terminal-sheet continuation invariance
statement: Fix chosen skeletons along based paths. Let $y$ lie in the terminal sheet of $p$, and let $p′$ be endpoint-fixed homotopic to the path obtained by appending the sheet path from $p$ to $π(y)$. If homotopies give grid walks and terminal-sheet extension preserves the endpoint formula, then $F_{S(p′)}(π(y))=F_{S(p)}(π(y))$.
proof: The homotopy-grid walk identifies the terminal formulas for $p′$ and the appended path. Compose this with the local-extension equality between the appended path and $p$.
-/
theorem pathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyPrinciple_of_homotopyGridWalk_and_localExtension
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton x₀ g localModels p)
    (hGrid :
      PathLocalTransitionBasedWeakHandoffHomotopyGridWalkPrinciple
        x₀ g localModels basedWeakHandoffAlong)
    (hLocal :
      PathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple
        x₀ g localModels basedWeakHandoffAlong) :
    PathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyPrinciple
      x₀ g localModels basedWeakHandoffAlong := by
  intro x p y' hy' p' hp'
  rcases hGrid hp' with ⟨W⟩
  exact
    W.terminalFormulaAt_start_eq_end.trans
      (hLocal p hy')


end HyperbolicMetric

end

end JJMath
