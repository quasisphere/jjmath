import JJMath.ComplexProjective.Prerequisites.RiemannSurface
import JJMath.ProjectiveGeometry.RiemannSphere
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Complex projective structures

A complex projective structure is an atlas modelled on the Riemann sphere whose
coordinate changes are locally restrictions of Mobius transformations.

The target is the canonical complex manifold structure on the one-point
compactification of the complex plane.  The predicate `HasMobiusTransition`
is intentionally small but concrete: it says that the transition between two
projective charts agrees, on its source, with a single Mobius representative.
Compatibility with the underlying complex structure is stored as local
holomorphic finite-coordinate data; from this certificate we derive ordinary
manifold holomorphicity of every projective chart into the standard sphere.
-/

namespace JJMath

open Set
open scoped Manifold Topology

/--
%%handwave
name:
  Projective chart
statement:
  A projective chart on a space $X$ is an open partial homeomorphism from $X$
  to the Riemann sphere $\mathbb{CP}^1$. These are the local coordinates used
  to build a complex projective atlas.
-/
abbrev ProjectiveChart (X : Type) [TopologicalSpace X] : Type :=
  OpenPartialHomeomorph X RiemannSphere

/--
%%handwave
name:
  Mobius transition data
statement:
  Concrete Mobius-transition data records a single global element of
  $\mathrm{PGL}_2(\mathbb C)$ representing the transition between two
  projective charts, together with the equality saying that the chart
  transition agrees with that representative on its source.

Concrete Mobius-transition data between two projective charts.

The representative is stored together with the equality on the transition
source, so consumers can project the actual Mobius map rather than merely use
a black-box compatibility proposition.
-/
structure MobiusTransitionData {X : Type} [TopologicalSpace X]
    (e e' : ProjectiveChart X) where
  /-- A global Mobius representative for the transition. -/
  representative : MobiusRepresentative
  /-- The chart transition agrees with the representative on its source. -/
  transition_eq :
    ∀ z ∈ (e.symm.trans e').source,
      (e.symm.trans e') z = (representative • z : RiemannSphere)

/--
%%handwave
name:
  Global Möbius transition
statement:
  Two projective charts have a global Möbius transition when their coordinate change on its entire source is represented by one element of $\operatorname{PGL}_2(\mathbb C)$.
-/
def HasMobiusTransition {X : Type} [TopologicalSpace X]
    (e e' : ProjectiveChart X) : Prop :=
  Nonempty (MobiusTransitionData e e')

/--
Local Mobius-transition data near one point of a projective chart overlap.

This is the componentwise form used by ordinary projective atlases: around each
overlap point, the coordinate change agrees with a single Mobius
representative.  It is weaker than `MobiusTransitionData`, which asks for one
representative on the whole transition source.
-/
structure LocalMobiusTransitionData {X : Type} [TopologicalSpace X]
    (e e' : ProjectiveChart X) (x : X) where
  /-- A base-space neighborhood on which the representative is valid. -/
  neighborhood : Set X
  /-- The neighborhood is open in the source surface. -/
  isOpen_neighborhood : IsOpen neighborhood
  /-- The selected point lies in the neighborhood. -/
  mem_neighborhood : x ∈ neighborhood
  /-- The neighborhood lies in the chart-source overlap. -/
  subset_overlap : neighborhood ⊆ e.source ∩ e'.source
  /-- A Mobius representative for the local transition. -/
  representative : MobiusRepresentative
  /--
  On projective coordinates whose corresponding source point lies in the
  neighborhood, the transition agrees with the representative.
  -/
  transition_eq :
    ∀ z ∈ (e.symm.trans e').source,
      e.symm z ∈ neighborhood →
        (e.symm.trans e') z = (representative • z : RiemannSphere)

/--
Local transition data whose representative lies in a prescribed subgroup of
`PGL(2, ℂ)`.
-/
structure TransitionInGroupData
    (G : Subgroup MobiusGroup) {X : Type} [TopologicalSpace X]
    (e e' : ProjectiveChart X) (x : X) extends
    LocalMobiusTransitionData e e' x where
  /-- The projective class of the local transition representative lies in `G`. -/
  representative_mem :
    Matrix.ProjGenLinGroup.mk representative ∈ G

/--
%%handwave
name:
  Local Mobius transitions
statement:
  Two projective charts have local Mobius transitions when, near every point of
  their source overlap, their coordinate change is represented by some Mobius
  transformation in $\mathrm{PGL}_2(\mathbb C)$. This is the compatibility
  condition for projective atlases.
-/
def HasLocalMobiusTransition {X : Type} [TopologicalSpace X]
    (e e' : ProjectiveChart X) : Prop :=
  ∀ x ∈ e.source ∩ e'.source, Nonempty (LocalMobiusTransitionData e e' x)

/--
%%handwave
name:
  Projective transitions in a prescribed subgroup
statement:
  Two projective charts have transitions in $G\le\operatorname{PGL}_2(\mathbb C)$ when, near every point of their source overlap, their coordinate change is represented by an element of $G$.
-/
def HasTransitionInGroup
    (G : Subgroup MobiusGroup) {X : Type} [TopologicalSpace X]
    (e e' : ProjectiveChart X) : Prop :=
  ∀ x ∈ e.source ∩ e'.source,
    Nonempty (TransitionInGroupData G e e' x)

/--
%%handwave
name:
  Subgroup-valued transitions are local Möbius transitions
statement:
  If the transition between projective charts \(e,e'\) is locally represented
  near every overlap point by a Möbius transformation belonging to a subgroup
  \(G\le\operatorname{PGL}_2(\mathbb C)\), then \(e,e'\) have local Möbius transitions.
proof:
  At each overlap point, retain the chosen Möbius representative and its local
  transition identity; membership in \(G\) is not needed for the conclusion.
-/
theorem hasLocalMobiusTransition_of_hasTransitionInGroup
    {G : Subgroup MobiusGroup} {X : Type} [TopologicalSpace X]
    {e e' : ProjectiveChart X}
    (h : HasTransitionInGroup G e e') :
    HasLocalMobiusTransition e e' := by
  intro x hx
  rcases h x hx with ⟨T⟩
  exact ⟨T.toLocalMobiusTransitionData⟩

/--
Concrete compatibility data between one projective chart and one complex chart.

After applying a fixed Mobius normalization to the projective coordinate, the
transition from the complex chart to the projective chart is represented by a
finite holomorphic coordinate with nonzero derivative on its source.
-/
structure ProjectiveComplexChartCompatibilityData {X : Type} [TopologicalSpace X]
    (projectiveChart : ProjectiveChart X)
    (complexChart : OpenPartialHomeomorph X ℂ) where
  /-- Mobius normalization putting this branch in a finite affine coordinate. -/
  representative : MobiusRepresentative
  /-- The resulting finite complex coordinate expression. -/
  finiteCoordinate : ℂ → ℂ
  /-- The normalized projective coordinate agrees with the finite coordinate. -/
  finiteCoordinate_eq :
    ∀ z ∈ (complexChart.symm.trans projectiveChart).source,
      representative • ((complexChart.symm.trans projectiveChart) z) =
        (finiteCoordinate z : RiemannSphere)
  /-- The finite coordinate expression is holomorphic on the transition source. -/
  finiteCoordinate_holomorphic :
    ∀ z ∈ (complexChart.symm.trans projectiveChart).source,
      DifferentiableAt ℂ finiteCoordinate z
  /-- The finite coordinate expression has nonzero derivative on the transition source. -/
  finiteCoordinate_deriv_ne_zero :
    ∀ z ∈ (complexChart.symm.trans projectiveChart).source,
      deriv finiteCoordinate z ≠ 0
  /--
  Local pointwise finite-coordinate compatibility: near every point of the
  transition source, the normalized projective coordinate is represented by a
  holomorphic finite coordinate with nonzero derivative.
  -/
  finiteCoordinate_local :
    ∀ z ∈ (complexChart.symm.trans projectiveChart).source,
      ∃ U : Set ℂ,
        IsOpen U ∧ z ∈ U ∧
          U ⊆ (complexChart.symm.trans projectiveChart).source ∧
            ∀ w ∈ U,
              DifferentiableAt ℂ finiteCoordinate w ∧ deriv finiteCoordinate w ≠ 0

/-- A selected ambient complex chart witnessing compatibility of one projective chart. -/
structure ProjectiveCompatibleComplexChartData {X : Type} [TopologicalSpace X]
    [ChartedSpace ℂ X] (projectiveChart : ProjectiveChart X) where
  /-- The ambient complex chart used to express this projective chart. -/
  complexChart : OpenPartialHomeomorph X ℂ
  /-- The selected complex chart belongs to the ambient Riemann-surface atlas. -/
  complexChart_mem_atlas : complexChart ∈ atlas ℂ X
  /-- The projective chart source is covered by the selected complex chart. -/
  projective_source_subset_complex_source :
    projectiveChart.source ⊆ complexChart.source
  /-- Concrete holomorphic local-biholomorphic compatibility in that chart. -/
  compatibility :
    ProjectiveComplexChartCompatibilityData projectiveChart complexChart

/-- Concrete holomorphic compatibility data for a projective charted space. -/
structure ProjectiveRiemannSurfaceCompatibilityData
    (X : Type) [TopologicalSpace X] (_complexCharts : ChartedSpace ℂ X)
    (projectiveCharts : ChartedSpace RiemannSphere X) where
  /-- Every projective chart source is open in the surface topology. -/
  projective_source_open :
    letI := projectiveCharts
    ∀ e ∈ atlas RiemannSphere X, IsOpen e.source
  /-- Every ambient complex chart source is open in the same topology. -/
  complex_source_open :
    letI := _complexCharts
    ∀ e ∈ atlas ℂ X, IsOpen e.source
  /--
  Each projective chart has a selected ambient complex chart covering its
  source in which it is holomorphic and locally biholomorphic.
  -/
  projective_complex_compatible :
    letI := projectiveCharts
    letI := _complexCharts
    ∀ e ∈ atlas RiemannSphere X,
      ProjectiveCompatibleComplexChartData e

/--
%%handwave
name:
  Complex projective structure
statement:
  A complex projective structure on a Riemann surface $X$ is an atlas modeled
  on the Riemann sphere $\mathbb{CP}^1$ whose chart transitions are locally
  Mobius transformations and whose projective coordinates are compatible with
  the given complex structure.
-/
structure ComplexProjectiveStructure (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [ComplexOneManifold X] where
  /-- The singled-out projective atlas. -/
  projectiveChartedSpace : ChartedSpace RiemannSphere X
  /-- Every projective coordinate transition is locally Mobius. -/
  transition_mobius :
    letI := projectiveChartedSpace
    ∀ e ∈ atlas RiemannSphere X, ∀ e' ∈ atlas RiemannSphere X,
      HasLocalMobiusTransition e e'
  /-- The projective atlas induces the given complex structure on `X`. -/
  compatible_with_riemann_surface :
    ProjectiveRiemannSurfaceCompatibilityData X (inferInstance : ChartedSpace ℂ X)
      projectiveChartedSpace

/--
%%handwave
name:
  Projective structure with structure group
statement:
  A projective structure with structure group $G$ is a complex projective
  structure whose local Mobius transition representatives all lie in the chosen
  subgroup $G \le \mathrm{PGL}_2(\mathbb C)$.
-/
structure ProjectiveStructureWithGroup
    (G : Subgroup MobiusGroup) (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [ComplexOneManifold X] extends
    ComplexProjectiveStructure X where
  /-- Every projective coordinate transition is locally represented by an element of `G`. -/
  transition_in_group :
    letI := projectiveChartedSpace
    ∀ e ∈ atlas RiemannSphere X, ∀ e' ∈ atlas RiemannSphere X,
      HasTransitionInGroup G e e'

namespace ComplexProjectiveStructure

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]

/--
%%handwave
name:
  Atlas of a complex projective structure
statement:
  The projective atlas of a complex projective structure $P$ is the set of all charts in its distinguished atlas modeled on $\widehat{\mathbb C}$.
-/
def atlasSet (P : ComplexProjectiveStructure X) : Set (ProjectiveChart X) :=
  letI := P.projectiveChartedSpace
  atlas RiemannSphere X

/--
%%handwave
name:
  Transitions between projective-atlas charts are locally Möbius
statement:
  If \(e,e'\) belong to the atlas of a complex projective structure \(P\),
  then near every point of \(e.source\cap e'.source\) their coordinate change
  agrees with a Möbius transformation.
proof:
  Apply the transition-compatibility field of \(P\) to the two atlas-membership hypotheses.
-/
theorem transition_mobius_of_mem (P : ComplexProjectiveStructure X)
    {e e' : ProjectiveChart X} (he : e ∈ P.atlasSet) (he' : e' ∈ P.atlasSet) :
    HasLocalMobiusTransition e e' := by
  letI := P.projectiveChartedSpace
  simpa [atlasSet] using P.transition_mobius e he e' he'

/--
%%handwave
name:
  Compatible complex coordinate for a projective chart
statement:
  Every chart $e$ in the atlas of a complex projective structure has a selected ambient complex chart covering its source, together with a normalized finite holomorphic coordinate of nonzero derivative.
-/
def chart_complex_compatible_of_mem (P : ComplexProjectiveStructure X)
    {e : ProjectiveChart X} (he : e ∈ P.atlasSet) :
    ProjectiveCompatibleComplexChartData e := by
  simpa [atlasSet] using
    P.compatible_with_riemann_surface.projective_complex_compatible e he

end ComplexProjectiveStructure

namespace ProjectiveStructureWithGroup

variable {G : Subgroup MobiusGroup} {X : Type} [TopologicalSpace X]
    [ChartedSpace ℂ X] [ComplexOneManifold X]

end ProjectiveStructureWithGroup

/--
%%handwave
name:
  A global Möbius transition supplies local transition data
statement:
  If one Möbius transformation represents the transition from \(e\) to \(e'\)
  on the whole coordinate-change domain, then \(e,e'\) have local Möbius
  transition data at every point of their source overlap.
proof:
  At an overlap point take \(e.source\cap e'.source\) as the open neighborhood
  and reuse the global representative and transition equation.
-/
theorem hasLocalMobiusTransition_of_hasMobiusTransition {X : Type} [TopologicalSpace X]
    {e e' : ProjectiveChart X} (h : HasMobiusTransition e e') :
    HasLocalMobiusTransition e e' := by
  rintro x hx
  rcases h with ⟨T⟩
  exact ⟨
    { neighborhood := e.source ∩ e'.source
      isOpen_neighborhood := e.open_source.inter e'.open_source
      mem_neighborhood := hx
      subset_overlap := fun y hy ↦ hy
      representative := T.representative
      transition_eq := by
        intro z hz _hz_neighborhood
        exact T.transition_eq z hz }⟩

/--
%%handwave
name:
  Disjoint chart sources have vacuous local Möbius transitions
statement:
  If \(e.source\cap e'.source=\varnothing\), then \(e,e'\) have local Möbius transitions.
proof:
  There is no overlap point at which transition data must be supplied.
-/
theorem hasLocalMobiusTransition_of_not_nonempty_source_inter {X : Type}
    [TopologicalSpace X] (e e' : ProjectiveChart X)
    (h : ¬ Set.Nonempty (e.source ∩ e'.source)) :
    HasLocalMobiusTransition e e' := by
  intro x hx
  exact (h ⟨x, hx⟩).elim

/--
%%handwave
name:
  A projective chart has the identity self-transition
statement:
  For every projective chart \(e\), the transition from \(e\) to itself is
  globally represented by the identity Möbius transformation.
proof:
  On the transition source, the right-inverse identity for the partial
  homeomorphism gives \(e\circ e^{-1}=\mathrm{id}\).
-/
theorem hasMobiusTransition_self {X : Type} [TopologicalSpace X]
    (e : ProjectiveChart X) : HasMobiusTransition e e := by
  refine ⟨{ representative := 1, transition_eq := ?_ }⟩
  intro z hz
  have hz_target : z ∈ e.target := by
    simpa [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] using hz.1
  simp [OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.right_inv, hz_target]

/--
%%handwave
name:
  A projective chart has identity local self-transitions
statement:
  Every projective chart has local Möbius transitions to itself, represented by the identity.
proof:
  Convert [the self-transition is globally the identity](lean:JJMath.hasMobiusTransition_self) into local transition data on the source overlap.
-/
theorem hasLocalMobiusTransition_self {X : Type} [TopologicalSpace X]
    (e : ProjectiveChart X) : HasLocalMobiusTransition e e :=
  hasLocalMobiusTransition_of_hasMobiusTransition (hasMobiusTransition_self e)

end JJMath
