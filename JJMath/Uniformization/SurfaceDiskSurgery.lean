import JJMath.Uniformization.LiouvilleExistence
import JJMath.RiemannianGeometry.SurfaceAnalysis
import Mathlib.Topology.UrysohnsLemma

/-!
# Surface disk surgery

This file records the local topological disk-surgery theorem for compact
smooth subsurfaces.  It is phrased for one homotopy square whose boundary is
already in the subsurface.
-/

namespace JJMath

open Set
open scoped Manifold Topology ContDiff

namespace Uniformization

/--
%%handwave
name:
  Complement component
statement:
  A subset \(U\) is a component of \(S\) when it is nonempty, preconnected,
  contained in \(S\), and maximal among preconnected subsets of \(S\) that
  meet it.
-/
def IsComplementComponent {X : Type} [TopologicalSpace X] (U S : Set X) : Prop :=
  U ⊆ S ∧ U.Nonempty ∧ IsPreconnected U ∧
    ∀ V : Set X, V ⊆ S → IsPreconnected V → (U ∩ V).Nonempty → V ⊆ U

/--
%%handwave
name:
  Boundary of the homotopy square
statement:
  The boundary of the parameter square consists of the four sides.
-/
def unitSquareBoundary : Set (unitInterval × unitInterval) :=
  {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1}

/--
%%handwave
name:
  The homotopy-square boundary is closed
statement:
  The union of the four sides of the parameter square is a closed subset of
  the square.
proof:
  Each side is the inverse image of a point under one of the coordinate
  projections, hence is closed.  A finite union of closed sets is closed.
-/
theorem unitSquareBoundary_isClosed :
    IsClosed unitSquareBoundary := by
  have hleft : IsClosed {z : unitInterval × unitInterval | z.1 = 0} :=
    isClosed_eq continuous_fst continuous_const
  have hright : IsClosed {z : unitInterval × unitInterval | z.1 = 1} :=
    isClosed_eq continuous_fst continuous_const
  have hbottom : IsClosed {z : unitInterval × unitInterval | z.2 = 0} :=
    isClosed_eq continuous_snd continuous_const
  have htop : IsClosed {z : unitInterval × unitInterval | z.2 = 1} :=
    isClosed_eq continuous_snd continuous_const
  simpa [unitSquareBoundary, setOf_or] using
    hleft.union (hright.union (hbottom.union htop))

/--
%%handwave
name:
  The homotopy-square interior is open
statement:
  The complement of the four sides of the parameter square is open.
proof:
  It is the complement of a closed subset.
-/
theorem unitSquareBoundary_isOpen_compl :
    IsOpen (unitSquareBoundaryᶜ : Set (unitInterval × unitInterval)) :=
  unitSquareBoundary_isClosed.isOpen_compl

/-- The part of the parameter square whose image lies in the exterior of `closure F`. -/
def pathHomotopyExteriorSet {X : Type} [TopologicalSpace X]
    {F : Set X} {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) : Set (unitInterval × unitInterval) :=
  H ⁻¹' (closure F)ᶜ

/-- The part of the parameter square whose image lies on the frontier of `F`. -/
def pathHomotopyFrontierPreimage {X : Type} [TopologicalSpace X]
    {F : Set X} {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) : Set (unitInterval × unitInterval) :=
  H ⁻¹' frontier F

/--
%%handwave
name:
  Homotopy squares have compact image
statement:
  The image of a path homotopy square is compact.
proof:
  The parameter square is compact and the homotopy is continuous.
-/
theorem pathHomotopy_range_isCompact
    {X : Type} [TopologicalSpace X] {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) :
    IsCompact (range H) := by
  simpa [image_univ] using
    (isCompact_univ.image (ContinuousMap.HomotopyWith.continuous H))

/--
%%handwave
name:
  Exterior preimages are open in the square
statement:
  The part of a homotopy square mapping outside \(\overline F\) is open.
proof:
  The complement of \(\overline F\) is open and the homotopy is continuous.
-/
theorem pathHomotopyExteriorSet_isOpen
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) :
    IsOpen (pathHomotopyExteriorSet (F := F) H) := by
  exact isClosed_closure.isOpen_compl.preimage
    (ContinuousMap.HomotopyWith.continuous H)

/--
%%handwave
name:
  Frontier preimages are closed in the square
statement:
  The part of a homotopy square mapping to the frontier of \(F\) is closed in
  the parameter square.
proof:
  The frontier is closed and the homotopy is continuous.
-/
theorem pathHomotopyFrontierPreimage_isClosed
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) :
    IsClosed (pathHomotopyFrontierPreimage (F := F) H) := by
  exact isClosed_frontier.preimage
    (ContinuousMap.HomotopyWith.continuous H)

/--
%%handwave
name:
  Frontier preimages are compact
statement:
  The part of a homotopy square mapping to the frontier of \(F\) is compact.
proof:
  It is a closed subset of the compact parameter square.
-/
theorem pathHomotopyFrontierPreimage_isCompact
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) :
    IsCompact (pathHomotopyFrontierPreimage (F := F) H) := by
  exact IsCompact.of_isClosed_subset isCompact_univ
    (pathHomotopyFrontierPreimage_isClosed (F := F) H)
    (by intro z _hz; exact mem_univ z)

/--
%%handwave
name:
  Compact closures have compact frontiers
statement:
  If \(\overline F\) is compact, then the frontier of \(F\) is compact.
proof:
  The frontier is closed and contained in \(\overline F\).
-/
theorem frontier_isCompact_of_closure_isCompact
    {X : Type} [TopologicalSpace X] {F : Set X}
    (hF_compact : IsCompact (closure F)) :
    IsCompact (frontier F) :=
  hF_compact.of_isClosed_subset isClosed_frontier frontier_subset_closure

/--
%%handwave
name:
  Frontier-hit images are compact
statement:
  The image of the frontier preimage of a homotopy square is compact.
proof:
  The frontier preimage is compact and the homotopy is continuous.
-/
theorem pathHomotopy_frontierImage_isCompact
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) :
    IsCompact (H '' pathHomotopyFrontierPreimage (F := F) H) :=
  (pathHomotopyFrontierPreimage_isCompact (F := F) H).image
    (ContinuousMap.HomotopyWith.continuous H)

/--
%%handwave
name:
  Frontier-hit images lie on the frontier
statement:
  The image of the frontier preimage of a homotopy square lies in the
  frontier of \(F\).
-/
theorem pathHomotopy_frontierImage_subset_frontier
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) :
    H '' pathHomotopyFrontierPreimage (F := F) H ⊆ frontier F := by
  rintro x ⟨z, hz, rfl⟩
  exact hz

/--
%%handwave
name:
  Homotopy image intersected with the frontier is compact
statement:
  The part of a compact homotopy-square image that lies on the frontier of
  \(F\) is compact.
proof:
  The homotopy-square image is compact, and the frontier of \(F\) is closed.
-/
theorem pathHomotopy_range_inter_frontier_isCompact
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) :
    IsCompact (range H ∩ frontier F) :=
  (pathHomotopy_range_isCompact H).inter_right isClosed_frontier

/--
%%handwave
name:
  Frontier-hit images lie in the frontier part of the homotopy image
statement:
  The image of the frontier preimage is contained in the intersection of the
  homotopy-square image with the frontier of \(F\).
-/
theorem pathHomotopy_frontierImage_subset_range_inter_frontier
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) :
    H '' pathHomotopyFrontierPreimage (F := F) H ⊆ range H ∩ frontier F := by
  rintro x ⟨z, hz, rfl⟩
  exact ⟨⟨z, rfl⟩, hz⟩

/--
%%handwave
name:
  Frontier push weight data
statement:
  A frontier push weight for a homotopy square is a continuous function on
  the parameter square that is equal to one on the frontier preimage, equal
  to zero on the square boundary, and takes values in \([0,1]\).
-/
structure PathHomotopyFrontierPushWeightData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) : Type where
  weight : C(unitInterval × unitInterval, ℝ)
  zero_on_boundary : EqOn weight 0 unitSquareBoundary
  one_on_frontier :
    EqOn weight 1 (pathHomotopyFrontierPreimage (F := F) H)
  range_mem_Icc : ∀ z, weight z ∈ Icc (0 : ℝ) 1

/--
%%handwave
name:
  Frontier preimages have continuous push weights
statement:
  If the frontier preimage of a homotopy square lies away from the square
  boundary, then there is a continuous frontier push weight: it is one on the
  frontier preimage, zero on the square boundary, and valued in \([0,1]\).
proof:
  The square boundary and the frontier preimage are disjoint closed subsets
  of the normal parameter square.  Urysohn's lemma separates them by a
  continuous function.
-/
theorem exists_pathHomotopyFrontierPushWeightData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hFrontier_interior :
      pathHomotopyFrontierPreimage (F := F) H ⊆ unitSquareBoundaryᶜ) :
    ∃ _hdata : PathHomotopyFrontierPushWeightData (F := F) H, True := by
  have hdisj :
      Disjoint unitSquareBoundary (pathHomotopyFrontierPreimage (F := F) H) := by
    rw [disjoint_left]
    intro z hzBoundary hzFrontier
    exact hFrontier_interior hzFrontier hzBoundary
  rcases
      exists_continuous_zero_one_of_isClosed
        unitSquareBoundary_isClosed
        (pathHomotopyFrontierPreimage_isClosed (F := F) H)
        hdisj with
    ⟨w, hzero, hone, hrange⟩
  refine ⟨?_, trivial⟩
  exact
    { weight := w
      zero_on_boundary := hzero
      one_on_frontier := hone
      range_mem_Icc := hrange }

/--
%%handwave
name:
  Chosen frontier push weight
statement:
  Choose a continuous frontier push weight for a frontier preimage lying away
  from the square boundary.
-/
noncomputable def pathHomotopyFrontierPushWeightData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hFrontier_interior :
      pathHomotopyFrontierPreimage (F := F) H ⊆ unitSquareBoundaryᶜ) :
    PathHomotopyFrontierPushWeightData (F := F) H :=
  (exists_pathHomotopyFrontierPushWeightData
    (F := F) H hFrontier_interior).choose

/--
%%handwave
name:
  Supported frontier push weight data
statement:
  A supported frontier push weight is a continuous function on the homotopy
  square that is one on the frontier preimage, zero outside a prescribed open
  support, and takes values in \([0,1]\).
-/
structure PathHomotopySupportedFrontierPushWeightData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) (support : Set (unitInterval × unitInterval)) :
    Type where
  weight : C(unitInterval × unitInterval, ℝ)
  zero_off_support : EqOn weight 0 supportᶜ
  one_on_frontier :
    EqOn weight 1 (pathHomotopyFrontierPreimage (F := F) H)
  range_mem_Icc : ∀ z, weight z ∈ Icc (0 : ℝ) 1

/--
%%handwave
name:
  Supported frontier push weights are ordinary frontier push weights
statement:
  If the support of a supported frontier push weight lies away from the square
  boundary, then it also gives an ordinary frontier push weight vanishing on
  the square boundary.
proof:
  The square boundary is disjoint from the support, so vanishing off the
  support implies vanishing on the boundary.
-/
def PathHomotopySupportedFrontierPushWeightData.toFrontierPushWeightData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {support : Set (unitInterval × unitInterval)}
    (data :
      PathHomotopySupportedFrontierPushWeightData
        (F := F) H support)
    (hsupport_interior : support ⊆ unitSquareBoundaryᶜ) :
    PathHomotopyFrontierPushWeightData (F := F) H where
  weight := data.weight
  zero_on_boundary := by
    intro z hz
    exact data.zero_off_support (by
      intro hzsupport
      exact hsupport_interior hzsupport hz)
  one_on_frontier := data.one_on_frontier
  range_mem_Icc := data.range_mem_Icc

/--
%%handwave
name:
  Supported frontier push weights vanish on the square boundary
statement:
  If the support of a supported frontier push weight lies in the interior of
  the homotopy square, then the weight is zero on the square boundary.
proof:
  The square boundary is outside the support, and the supported weight
  vanishes off its support.
-/
theorem PathHomotopySupportedFrontierPushWeightData.zero_on_boundary
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {support : Set (unitInterval × unitInterval)}
    (data :
      PathHomotopySupportedFrontierPushWeightData
        (F := F) H support)
    (hsupport_interior : support ⊆ unitSquareBoundaryᶜ) :
    EqOn data.weight 0 unitSquareBoundary :=
  (data.toFrontierPushWeightData hsupport_interior).zero_on_boundary

/--
%%handwave
name:
  Supported frontier push weights force the frontier preimage into the support
statement:
  The frontier preimage of the homotopy square is contained in the support of
  any supported frontier push weight.
proof:
  On the frontier preimage the weight is one.  Off the support it is zero, so
  a frontier point cannot lie outside the support.
-/
theorem PathHomotopySupportedFrontierPushWeightData.frontier_subset_support
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {support : Set (unitInterval × unitInterval)}
    (data :
      PathHomotopySupportedFrontierPushWeightData
        (F := F) H support) :
    pathHomotopyFrontierPreimage (F := F) H ⊆ support := by
  intro z hz
  by_contra hzsupport
  have hzero : data.weight z = 0 := data.zero_off_support hzsupport
  have hone : data.weight z = 1 := data.one_on_frontier hz
  have h01 : (0 : ℝ) = 1 := by
    rw [← hzero, hone]
  exact zero_ne_one h01

/--
%%handwave
name:
  Frontier preimages have supported continuous push weights
statement:
  If an open support contains the frontier preimage of a homotopy square,
  then there is a continuous supported push weight equal to one on the
  frontier preimage and zero outside the support.
proof:
  The frontier preimage is closed and is disjoint from the closed complement
  of the open support.  Urysohn's lemma separates these two closed sets by a
  continuous function with values in \([0,1]\).
-/
theorem exists_pathHomotopySupportedFrontierPushWeightData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (support : Set (unitInterval × unitInterval))
    (hsupport_open : IsOpen support)
    (hcover :
      pathHomotopyFrontierPreimage (F := F) H ⊆ support) :
    ∃ _hdata :
      PathHomotopySupportedFrontierPushWeightData
        (F := F) H support,
        True := by
  have hdisj :
      Disjoint supportᶜ
        (pathHomotopyFrontierPreimage (F := F) H) := by
    rw [disjoint_left]
    intro z hzSupportCompl hzFrontier
    exact hzSupportCompl (hcover hzFrontier)
  rcases
      exists_continuous_zero_one_of_isClosed
        hsupport_open.isClosed_compl
        (pathHomotopyFrontierPreimage_isClosed (F := F) H)
        hdisj with
    ⟨w, hzero, hone, hrange⟩
  refine ⟨?_, trivial⟩
  exact
    { weight := w
      zero_off_support := hzero
      one_on_frontier := hone
      range_mem_Icc := hrange }

/--
%%handwave
name:
  Chosen supported frontier push weight
statement:
  Choose a supported continuous push weight for an open support containing
  the frontier preimage.
-/
noncomputable def pathHomotopySupportedFrontierPushWeightData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (support : Set (unitInterval × unitInterval))
    (hsupport_open : IsOpen support)
    (hcover :
      pathHomotopyFrontierPreimage (F := F) H ⊆ support) :
    PathHomotopySupportedFrontierPushWeightData (F := F) H support :=
  (exists_pathHomotopySupportedFrontierPushWeightData
    (F := F) H support hsupport_open hcover).choose

/--
%%handwave
name:
  Local smooth boundary chart data
statement:
  At a point of a smooth frontier, a local boundary-chart datum records a
  complex chart, a smooth real defining function with nonzero derivative, and
  an open neighborhood on which the domain is exactly the negative side and
  the frontier is exactly the zero set.
-/
structure LocalBoundaryChartData {X : Type} [TopologicalSpace X]
    [ChartedSpace ℂ X] {F : Set X} (x : X) : Type where
  chart : OpenPartialHomeomorph X ℂ
  chart_mem_atlas : chart ∈ atlas ℂ X
  mem_source : x ∈ chart.source
  definingFunction : ℂ → ℝ
  definingFunction_smooth :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) definingFunction (chart x)
  definingDerivative : ℂ →L[ℝ] ℝ
  definingFunction_deriv :
    HasFDerivAt definingFunction definingDerivative (chart x)
  definingDerivative_ne_zero : definingDerivative ≠ 0
  neighborhood : Set X
  isOpen_neighborhood : IsOpen neighborhood
  mem_neighborhood : x ∈ neighborhood
  subset_chart_source : neighborhood ⊆ chart.source
  local_model_on :
    ∀ y ∈ neighborhood,
      y ∈ chart.source ∧
        (y ∈ F ↔ definingFunction (chart y) < 0) ∧
          (y ∈ frontier F ↔ definingFunction (chart y) = 0)

/--
%%handwave
name:
  Smooth frontiers have local boundary-chart data
statement:
  Every point of a smooth frontier has local smooth boundary-chart data.
proof:
  This is the defining local model for a smooth boundary, shrunk from an
  eventual neighborhood statement to an open neighborhood.
-/
theorem exists_smoothBoundary_localBoundaryChartData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} (hF_smooth : HasSmoothBoundary F)
    (x : X) (hx : x ∈ frontier F) :
    ∃ _hdata : LocalBoundaryChartData (F := F) x, True := by
  rcases hF_smooth x hx with
    ⟨e, he_atlas, hx_source, r, hr_smooth, dr, hr_deriv, hdr_ne, hlocal⟩
  rcases mem_nhds_iff.mp hlocal with ⟨N, hNsub, hNopen, hxN⟩
  refine ⟨?_, trivial⟩
  exact
    { chart := e
      chart_mem_atlas := he_atlas
      mem_source := hx_source
      definingFunction := r
      definingFunction_smooth := hr_smooth.contDiffAt
      definingDerivative := dr
      definingFunction_deriv := hr_deriv
      definingDerivative_ne_zero := hdr_ne
      neighborhood := N
      isOpen_neighborhood := hNopen
      mem_neighborhood := hxN
      subset_chart_source := by
        intro y hy
        exact (hNsub hy).1
      local_model_on := by
        intro y hy
        exact hNsub hy }

/--
%%handwave
name:
  Chosen local smooth boundary-chart data
statement:
  Choose local smooth boundary-chart data at a point of a smooth frontier.
-/
noncomputable def smoothBoundary_localBoundaryChartData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} (hF_smooth : HasSmoothBoundary F)
    (x : X) (hx : x ∈ frontier F) :
    LocalBoundaryChartData (F := F) x :=
  (exists_smoothBoundary_localBoundaryChartData
    (F := F) hF_smooth x hx).choose

/--
%%handwave
name:
  Compact frontier subsets have finite smooth boundary-chart covers
statement:
  A compact subset of a smooth frontier is covered by finitely many local
  smooth boundary charts.
proof:
  The chosen local boundary-chart neighborhoods form an open cover of the
  compact set, so compactness gives a finite subcover.
-/
theorem smoothBoundary_compactFrontierSubset_finiteLocalBoundaryChartCover
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F K : Set X} (hF_smooth : HasSmoothBoundary F)
    (hK_compact : IsCompact K) (hK_frontier : K ⊆ frontier F) :
    ∃ t : Finset K,
      K ⊆
        ⋃ x ∈ t,
          (smoothBoundary_localBoundaryChartData
            (F := F) hF_smooth (x : X) (hK_frontier x.2)).neighborhood := by
  let U : K → Set X := fun x =>
    (smoothBoundary_localBoundaryChartData
      (F := F) hF_smooth (x : X) (hK_frontier x.2)).neighborhood
  have hU_open : ∀ x, IsOpen (U x) := by
    intro x
    exact
      (smoothBoundary_localBoundaryChartData
        (F := F) hF_smooth (x : X) (hK_frontier x.2)).isOpen_neighborhood
  have hcover : K ⊆ ⋃ x, U x := by
    intro y hy
    exact
      mem_iUnion_of_mem ⟨y, hy⟩
        (smoothBoundary_localBoundaryChartData
          (F := F) hF_smooth y (hK_frontier hy)).mem_neighborhood
  rcases hK_compact.elim_finite_subcover U hU_open hcover with ⟨t, ht⟩
  exact ⟨t, by simpa [U] using ht⟩

/--
%%handwave
name:
  Frontier-hit images have finite smooth boundary-chart covers
statement:
  The frontier values hit by a homotopy square are covered by finitely many
  smooth boundary charts.
proof:
  The frontier-hit image is compact and lies in the smooth frontier, so apply
  the finite chart-cover theorem for compact frontier subsets.
-/
theorem pathHomotopy_frontierImage_finiteLocalBoundaryChartCover
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) :
    ∃ t : Finset (H '' pathHomotopyFrontierPreimage (F := F) H),
      H '' pathHomotopyFrontierPreimage (F := F) H ⊆
        ⋃ x ∈ t,
          (smoothBoundary_localBoundaryChartData
            (F := F) hF_smooth (x : X)
            (pathHomotopy_frontierImage_subset_frontier
              (F := F) H x.2)).neighborhood := by
  exact
    smoothBoundary_compactFrontierSubset_finiteLocalBoundaryChartCover
      (F := F) hF_smooth
      (pathHomotopy_frontierImage_isCompact (F := F) H)
      (pathHomotopy_frontierImage_subset_frontier (F := F) H)

/--
%%handwave
name:
  Exterior excursions avoid the square boundary
statement:
  If the boundary of a homotopy square maps into \(F\), then every point of
  the square that maps outside \(\overline F\) lies away from the square
  boundary.
proof:
  A boundary point maps to \(F\), hence to \(\overline F\).
-/
theorem pathHomotopyExteriorSet_subset_compl_unitSquareBoundary
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hboundary : ∀ z, z ∈ unitSquareBoundary → H z ∈ F) :
    pathHomotopyExteriorSet (F := F) H ⊆ unitSquareBoundaryᶜ := by
  intro z hz hzb
  exact hz (subset_closure (hboundary z hzb))

/--
%%handwave
name:
  The first boundary path lies in the subsurface
statement:
  If the boundary of a homotopy square maps into \(F\), then the path on the
  left side of the square has image in \(F\).
proof:
  The left side of the parameter square is part of the square boundary.
-/
theorem pathHomotopy_sourcePath_mapsTo_of_boundary
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hboundary : ∀ z, z ∈ unitSquareBoundary → H z ∈ F) :
    MapsTo γ₀ univ F := by
  intro t _ht
  have hside : ((0, t) : unitInterval × unitInterval) ∈ unitSquareBoundary := by
    simp [unitSquareBoundary]
  have hHt : H (0, t) ∈ F := hboundary (0, t) hside
  simpa using hHt

/--
%%handwave
name:
  The second boundary path lies in the subsurface
statement:
  If the boundary of a homotopy square maps into \(F\), then the path on the
  right side of the square has image in \(F\).
proof:
  The right side of the parameter square is part of the square boundary.
-/
theorem pathHomotopy_targetPath_mapsTo_of_boundary
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hboundary : ∀ z, z ∈ unitSquareBoundary → H z ∈ F) :
    MapsTo γ₁ univ F := by
  intro t _ht
  have hside : ((1, t) : unitInterval × unitInterval) ∈ unitSquareBoundary := by
    simp [unitSquareBoundary]
  have hHt : H (1, t) ∈ F := hboundary (1, t) hside
  simpa using hHt

/--
%%handwave
name:
  Homotopy square endpoints lie in the subsurface
statement:
  If the boundary of a path homotopy square maps into \(F\), then the common
  endpoints of the two boundary paths lie in \(F\).
proof:
  Apply the boundary-path containment to the first path and evaluate it at
  the endpoints.
-/
theorem pathHomotopy_endpoints_mem_of_boundary
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hboundary : ∀ z, z ∈ unitSquareBoundary → H z ∈ F) :
    a ∈ F ∧ b ∈ F := by
  have hγ₀ : MapsTo γ₀ univ F :=
    pathHomotopy_sourcePath_mapsTo_of_boundary (F := F) H hboundary
  constructor
  · have h0 : γ₀ (0 : unitInterval) ∈ F := hγ₀ (by simp)
    simpa using h0
  · have h1 : γ₀ (1 : unitInterval) ∈ F := hγ₀ (by simp)
    simpa using h1

/--
%%handwave
name:
  Boundary paths determine the whole square boundary
statement:
  If the two path sides of a path homotopy have image in \(F\), then the
  entire boundary of the homotopy square maps into \(F\).
proof:
  The left and right sides are the two paths.  The bottom and top sides are
  the fixed path endpoints, which lie on those paths.
-/
theorem pathHomotopy_boundary_mapsTo_of_path_mapsTo
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hγ₀ : MapsTo γ₀ univ F)
    (hγ₁ : MapsTo γ₁ univ F) :
    ∀ z, z ∈ unitSquareBoundary → H z ∈ F := by
  rintro ⟨s, t⟩ hz
  change s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1 at hz
  rcases hz with hs0 | hs1 | ht0 | ht1
  · rw [hs0]
    have hHt : H (0, t) = γ₀ t := by
      simp
    rw [hHt]
    exact hγ₀ (by simp)
  · rw [hs1]
    have hHt : H (1, t) = γ₁ t := by
      simp
    rw [hHt]
    exact hγ₁ (by simp)
  · rw [ht0]
    have hHt : H (s, 0) = a := by
      simp
    rw [hHt]
    have h0 : γ₀ (0 : unitInterval) ∈ F := hγ₀ (by simp)
    simpa using h0
  · rw [ht1]
    have hHt : H (s, 1) = b := by
      simp
    rw [hHt]
    have h1 : γ₀ (1 : unitInterval) ∈ F := hγ₀ (by simp)
    simpa using h1

/--
%%handwave
name:
  Frontier preimages avoid the square boundary
statement:
  If the two path sides of a path homotopy have image in the open set \(F\),
  then no point of the square boundary maps to the frontier of \(F\).
proof:
  The whole square boundary maps into \(F\), while an open set is disjoint
  from its frontier.
-/
theorem pathHomotopyFrontierPreimage_subset_compl_unitSquareBoundary_of_path_mapsTo
    {X : Type} [TopologicalSpace X] {F : Set X}
    (hF_open : IsOpen F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hγ₀ : MapsTo γ₀ univ F)
    (hγ₁ : MapsTo γ₁ univ F) :
    pathHomotopyFrontierPreimage (F := F) H ⊆ unitSquareBoundaryᶜ := by
  intro z hz hzb
  have hzF : H z ∈ F :=
    pathHomotopy_boundary_mapsTo_of_path_mapsTo
      (F := F) H hγ₀ hγ₁ z hzb
  have hnot : H z ∉ frontier F := by
    intro hzFrontier
    have hzInter : H z ∈ F ∩ frontier F := ⟨hzF, hzFrontier⟩
    simp [hF_open.inter_frontier_eq] at hzInter
  exact hnot hz

/--
%%handwave
name:
  Closure-valued homotopies meet the complement only on the frontier
statement:
  If a homotopy square has image in \(\overline F\) and \(F\) is open, then a
  parameter point maps outside \(F\) exactly when it maps to the frontier of
  \(F\).
proof:
  For an open set, the frontier is \(\overline F\setminus F\).
-/
theorem pathHomotopy_not_mem_iff_mem_frontier_of_mapsTo_closure
    {X : Type} [TopologicalSpace X] {F : Set X}
    (hF_open : IsOpen F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hH_closure : ∀ z, H z ∈ closure F)
    (z : unitInterval × unitInterval) :
    H z ∉ F ↔ z ∈ pathHomotopyFrontierPreimage (F := F) H := by
  constructor
  · intro hzF
    rw [pathHomotopyFrontierPreimage]
    rw [hF_open.frontier_eq]
    exact ⟨hH_closure z, hzF⟩
  · intro hzFrontier hzF
    have hnot : H z ∉ F := by
      rw [pathHomotopyFrontierPreimage, hF_open.frontier_eq] at hzFrontier
      exact hzFrontier.2
    exact hnot hzF

/--
%%handwave
name:
  Closure-valued homotopies with empty frontier preimage lie in the open side
statement:
  If a homotopy square has image in \(\overline F\), \(F\) is open, and no
  parameter point maps to the frontier of \(F\), then the homotopy already has
  image in \(F\).
proof:
  A point of the closure outside \(F\) would be a frontier point.
-/
theorem pathHomotopy_mapsTo_open_of_mapsTo_closure_and_frontierPreimage_empty
    {X : Type} [TopologicalSpace X] {F : Set X}
    (hF_open : IsOpen F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hH_closure : ∀ z, H z ∈ closure F)
    (hFrontier_empty : pathHomotopyFrontierPreimage (F := F) H = ∅) :
    ∀ z, H z ∈ F := by
  intro z
  by_contra hzF
  have hzFrontier :
      z ∈ pathHomotopyFrontierPreimage (F := F) H :=
    (pathHomotopy_not_mem_iff_mem_frontier_of_mapsTo_closure
      (F := F) hF_open H hH_closure z).mp hzF
  simp [hFrontier_empty] at hzFrontier

/--
%%handwave
name:
  Closure-valued homotopies are open-sided away from the frontier preimage
statement:
  If a homotopy square has image in \(\overline F\) and \(F\) is open, then
  every parameter point outside the frontier preimage already maps into
  \(F\).
proof:
  For an open set, a point of \(\overline F\) that is not in \(F\) lies on
  the frontier of \(F\).
-/
theorem pathHomotopy_mapsTo_open_on_compl_frontierPreimage_of_mapsTo_closure
    {X : Type} [TopologicalSpace X] {F : Set X}
    (hF_open : IsOpen F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hH_closure : ∀ z, H z ∈ closure F) :
    MapsTo H (pathHomotopyFrontierPreimage (F := F) H)ᶜ F := by
  intro z hzFrontierCompl
  by_contra hzF
  exact hzFrontierCompl
    ((pathHomotopy_not_mem_iff_mem_frontier_of_mapsTo_closure
      (F := F) hF_open H hH_closure z).mp hzF)

/--
%%handwave
name:
  Supported frontier push weights leave only open-side values off the support
statement:
  If a closure-valued homotopy square has a supported frontier push weight,
  then outside the support the original square already takes values in
  \(F\).
proof:
  The supported weight forces the entire frontier preimage into the support.
  Away from the support there are therefore no frontier points, and a
  closure-valued map with no frontier value is already on the open side.
-/
theorem PathHomotopySupportedFrontierPushWeightData.mapsTo_open_on_support_compl
    {X : Type} [TopologicalSpace X] {F : Set X}
    (hF_open : IsOpen F)
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hH_closure : ∀ z, H z ∈ closure F)
    {support : Set (unitInterval × unitInterval)}
    (data :
      PathHomotopySupportedFrontierPushWeightData
        (F := F) H support) :
    MapsTo H supportᶜ F := by
  intro z hzSupportCompl
  exact
    pathHomotopy_mapsTo_open_on_compl_frontierPreimage_of_mapsTo_closure
      (F := F) hF_open H hH_closure
      (by
        intro hzFrontier
        exact hzSupportCompl (data.frontier_subset_support hzFrontier))

/--
%%handwave
name:
  Closure-valued homotopies with empty frontier preimage need no collar push
statement:
  If a closure-valued homotopy square has empty frontier preimage, then it is
  already a homotopy whose image lies in \(F\).
-/
theorem pathHomotopy_in_closure_pushes_into_open_of_frontierPreimage_empty
    {X : Type} [TopologicalSpace X] {F : Set X}
    (hF_open : IsOpen F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hH_closure : ∀ z, H z ∈ closure F)
    (hFrontier_empty : pathHomotopyFrontierPreimage (F := F) H = ∅) :
    ∃ H' : γ₀.Homotopy γ₁, ∀ z, H' z ∈ F :=
  ⟨H,
    pathHomotopy_mapsTo_open_of_mapsTo_closure_and_frontierPreimage_empty
      (F := F) hF_open H hH_closure hFrontier_empty⟩

/--
%%handwave
name:
  Homotopies already in the subsurface need no surgery
statement:
  If a path homotopy square already has image in \(F\), then it is itself the
  required pushed-off homotopy.
-/
theorem pathHomotopy_pushes_off_of_mapsTo
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hH : ∀ z, H z ∈ F) :
    ∃ H' : γ₀.Homotopy γ₁, ∀ z, H' z ∈ F :=
  ⟨H, hH⟩

/--
%%handwave
name:
  Homotopies in the closure have no exterior set
statement:
  If a path homotopy square has image in \(\overline F\), then its exterior
  preimage is empty.
-/
theorem pathHomotopyExteriorSet_eq_empty_of_mapsTo_closure
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hH : ∀ z, H z ∈ closure F) :
    pathHomotopyExteriorSet (F := F) H = ∅ := by
  ext z
  constructor
  · intro hz
    exact False.elim (hz (hH z))
  · intro hz
    exact False.elim hz

/--
%%handwave
name:
  Empty exterior set means the homotopy lies in the closure
statement:
  If the exterior preimage of a path homotopy square is empty, then the
  homotopy has image in \(\overline F\).
-/
theorem pathHomotopy_mapsTo_closure_of_exteriorSet_eq_empty
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hExterior_empty : pathHomotopyExteriorSet (F := F) H = ∅) :
    ∀ z, H z ∈ closure F := by
  intro z
  by_contra hz
  have hzExterior : z ∈ pathHomotopyExteriorSet (F := F) H := by
    simpa [pathHomotopyExteriorSet] using hz
  simp [hExterior_empty] at hzExterior

/--
%%handwave
name:
  Empty exterior set gives a homotopy in the closure
statement:
  If the exterior preimage of a path homotopy square is empty, then the
  original homotopy already has image in \(\overline F\).
-/
theorem pathHomotopy_pushes_to_closure_of_exteriorSet_eq_empty
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hExterior_empty : pathHomotopyExteriorSet (F := F) H = ∅) :
    ∃ H' : γ₀.Homotopy γ₁, ∀ z, H' z ∈ closure F :=
  ⟨H, pathHomotopy_mapsTo_closure_of_exteriorSet_eq_empty
    (F := F) H hExterior_empty⟩

/--
%%handwave
name:
  Closed parameter disk
statement:
  A closed parameter disk is a subset of the square homeomorphic to a closed
  Euclidean disk.
-/
def IsClosedParamDisk (D : Set (unitInterval × unitInterval)) : Prop :=
  Nonempty (D ≃ₜ Metric.closedBall (0 : ℂ) 1)

/--
%%handwave
name:
  Regular closed parameter disk
statement:
  A regular closed parameter disk is a closed parameter disk whose ambient
  interior is a nonempty preconnected open disk dense in the closed disk, and
  whose frontier is a circle.
-/
structure IsRegularClosedParamDisk
    (D : Set (unitInterval × unitInterval)) : Prop where
  closedParamDisk : IsClosedParamDisk D
  closure_interior_eq : closure (interior D) = D
  interior_nonempty : (interior D).Nonempty
  interior_preconnected : IsPreconnected (interior D)
  interior_homeomorph_openDisk :
    Nonempty (interior D ≃ₜ Metric.ball (0 : ℂ) 1)
  frontier_homeomorph_circle :
    Nonempty (frontier D ≃ₜ Metric.sphere (0 : ℂ) 1)

/--
%%handwave
name:
  Closed parameter disks are compact
statement:
  A closed parameter disk is compact.
proof:
  It is homeomorphic to a compact Euclidean closed disk.
-/
theorem IsClosedParamDisk.isCompact
    {D : Set (unitInterval × unitInterval)}
    (hD : IsClosedParamDisk D) :
    IsCompact D := by
  rcases hD with ⟨e⟩
  haveI : CompactSpace (Metric.closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp (ProperSpace.isCompact_closedBall (0 : ℂ) 1)
  haveI : CompactSpace D := Homeomorph.compactSpace e.symm
  exact isCompact_iff_compactSpace.mpr inferInstance

/--
%%handwave
name:
  Closed parameter disks are closed
statement:
  A closed parameter disk is closed in the homotopy square.
proof:
  It is compact, and the homotopy square is Hausdorff.
-/
theorem IsClosedParamDisk.isClosed
    {D : Set (unitInterval × unitInterval)}
    (hD : IsClosedParamDisk D) :
    IsClosed D :=
  hD.isCompact.isClosed

/--
%%handwave
name:
  Regular closed parameter disks are closed parameter disks
statement:
  A regular closed parameter disk is, in particular, a closed parameter disk.
-/
theorem IsRegularClosedParamDisk.isClosedParamDisk
    {D : Set (unitInterval × unitInterval)}
    (hD : IsRegularClosedParamDisk D) :
    IsClosedParamDisk D :=
  hD.closedParamDisk

/--
%%handwave
name:
  The interior is dense in a regular closed parameter disk
statement:
  In a regular closed parameter disk, the ambient interior is dense in the
  closed disk, considered as a subtype.
proof:
  The closure of the ambient interior is the whole closed disk.
-/
theorem IsRegularClosedParamDisk.dense_interiorSubtype
    {D : Set (unitInterval × unitInterval)}
    (hD : IsRegularClosedParamDisk D) :
    Dense ({z : D | (z : unitInterval × unitInterval) ∈ interior D} : Set D) := by
  rw [Subtype.dense_iff]
  intro z hzD
  have himage :
      ((↑) : D → unitInterval × unitInterval) ''
          ({z : D | (z : unitInterval × unitInterval) ∈ interior D} : Set D) =
        interior D := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, interior_subset hy⟩, hy, rfl⟩
  have hzclosure :
      (z : unitInterval × unitInterval) ∈ closure (interior D) := by
    simpa [hD.closure_interior_eq] using hzD
  simpa [himage] using hzclosure

/--
%%handwave
name:
  Finite exterior-excursion data
statement:
  A homotopy square is in finite exterior-excursion position relative to
  \(F\) if the part mapping outside \(\overline F\) is the union of the
  interiors of finitely many pairwise disjoint closed parameter disks, all
  lying away from the square boundary, with disk interiors mapping outside
  \(\overline F\) and disk boundaries mapping to the frontier of \(F\).
-/
structure FiniteExteriorExcursionData {X : Type} [TopologicalSpace X]
    {F : Set X} {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) : Type 1 where
  ι : Type
  finite : Fintype ι
  disk : ι → Set (unitInterval × unitInterval)
  disk_closed : ∀ i, IsClosedParamDisk (disk i)
  disk_regular : ∀ i, IsRegularClosedParamDisk (disk i)
  disk_subset_interior : ∀ i, disk i ⊆ unitSquareBoundaryᶜ
  exterior_eq :
    pathHomotopyExteriorSet (F := F) H = ⋃ i, interior (disk i)
  pairwise_disjoint_interiors :
    Pairwise fun i j => Disjoint (interior (disk i)) (interior (disk j))
  interior_maps_to_exterior :
    ∀ i, MapsTo H (interior (disk i)) (closure F)ᶜ
  frontier_maps_to_frontier :
    ∀ i, MapsTo H (frontier (disk i)) (frontier F)

/--
%%handwave
name:
  Number of finite exterior-excursion disks
statement:
  The number of disks in finite exterior-excursion data is the cardinality of
  its finite index set.
-/
def finiteExteriorExcursionDataCard
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b} {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H) : ℕ :=
  @Fintype.card hdata.ι hdata.finite

/--
%%handwave
name:
  Zero finite exterior-excursion count is equivalent to no indexed disks
statement:
  Finite exterior-excursion data has zero disks exactly when its index set is
  empty.
-/
theorem finiteExteriorExcursionDataCard_eq_zero_iff
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b} {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H) :
    finiteExteriorExcursionDataCard hdata = 0 ↔ IsEmpty hdata.ι := by
  exact @Fintype.card_eq_zero_iff hdata.ι hdata.finite

/--
%%handwave
name:
  Positive finite exterior-excursion count is equivalent to having an indexed disk
statement:
  Finite exterior-excursion data has positive disk count exactly when its
  index set is nonempty.
-/
theorem finiteExteriorExcursionDataCard_pos_iff
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b} {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H) :
    0 < finiteExteriorExcursionDataCard hdata ↔ Nonempty hdata.ι := by
  exact @Fintype.card_pos_iff hdata.ι hdata.finite

/--
%%handwave
name:
  Finite exterior-excursion position
statement:
  A homotopy between two fixed paths is in finite exterior-excursion position
  relative to \(F\) if its square boundary maps to \(F\) and it carries
  finite exterior-excursion data.
-/
structure FiniteExteriorExcursionPosition {X : Type} [TopologicalSpace X]
    {F : Set X} {a b : X} (γ₀ γ₁ : Path a b) : Type 1 where
  homotopy : γ₀.Homotopy γ₁
  boundary_mapsTo : ∀ z, z ∈ unitSquareBoundary → homotopy z ∈ F
  data : FiniteExteriorExcursionData (F := F) homotopy

/--
%%handwave
name:
  Selected exterior-excursion disk data
statement:
  A selected exterior-excursion disk is one disk from finite exterior
  excursion data, together with its closed-disk structure, containment in the
  interior of the homotopy square, and the facts that its interior maps
  outside \(\overline F\) while its frontier maps to the frontier of \(F\).
-/
structure SelectedExteriorExcursionDiskData {X : Type} [TopologicalSpace X]
    {F : Set X} {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) (hdata : FiniteExteriorExcursionData (F := F) H) :
    Type 1 where
  index : hdata.ι
  disk_closed : IsClosedParamDisk (hdata.disk index)
  disk_regular : IsRegularClosedParamDisk (hdata.disk index)
  disk_subset_interior : hdata.disk index ⊆ unitSquareBoundaryᶜ
  interior_maps_to_exterior :
    MapsTo H (interior (hdata.disk index)) (closure F)ᶜ
  frontier_maps_to_frontier :
    MapsTo H (frontier (hdata.disk index)) (frontier F)

/--
%%handwave
name:
  Nonempty finite exterior data selects an exterior disk
statement:
  If finite exterior-excursion data has a nonempty index set, then one
  exterior-excursion disk can be selected with all of its recorded
  disk-surgery properties.
proof:
  Choose an index and read the corresponding fields from the finite
  exterior-excursion data.
-/
theorem exists_selectedExteriorExcursionDiskData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hdata_nonempty : Nonempty hdata.ι) :
    ∃ _hselected : SelectedExteriorExcursionDiskData (F := F) H hdata, True := by
  let i : hdata.ι := Classical.choice hdata_nonempty
  refine ⟨?_, trivial⟩
  exact
    { index := i
      disk_closed := hdata.disk_closed i
      disk_regular := hdata.disk_regular i
      disk_subset_interior := hdata.disk_subset_interior i
      interior_maps_to_exterior := hdata.interior_maps_to_exterior i
      frontier_maps_to_frontier := hdata.frontier_maps_to_frontier i }

/--
%%handwave
name:
  Chosen selected exterior-excursion disk data
statement:
  Choose one exterior-excursion disk from nonempty finite exterior data.
-/
noncomputable def selectedExteriorExcursionDiskData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hdata_nonempty : Nonempty hdata.ι) :
    SelectedExteriorExcursionDiskData (F := F) H hdata :=
  (exists_selectedExteriorExcursionDiskData
    (F := F) H hdata hdata_nonempty).choose

/--
%%handwave
name:
  Selected exterior disk lies in the square interior
statement:
  The selected exterior-excursion disk lies away from the boundary of the
  homotopy square.
-/
theorem selectedExteriorExcursionDisk_subset_squareInterior
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    hdata.disk hselected.index ⊆ unitSquareBoundaryᶜ :=
  hselected.disk_subset_interior

/--
%%handwave
name:
  Selected exterior disk interiors lie in the square interior
statement:
  The interior of the selected exterior-excursion disk lies away from the
  boundary of the homotopy square.
proof:
  The disk itself lies in the square interior, and the interior of a set is
  contained in the set.
-/
theorem selectedExteriorExcursionDisk_interior_subset_squareInterior
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    interior (hdata.disk hselected.index) ⊆ unitSquareBoundaryᶜ := by
  intro z hz
  exact
    selectedExteriorExcursionDisk_subset_squareInterior
      (F := F) H hdata hselected (interior_subset hz)

/--
%%handwave
name:
  The square boundary avoids selected exterior-disk interiors
statement:
  The boundary of the homotopy square is disjoint from the interior of a
  selected exterior-excursion disk.
proof:
  The selected disk interior lies in the interior of the homotopy square.
-/
theorem unitSquareBoundary_subset_compl_selectedExteriorExcursionDisk_interior
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    unitSquareBoundary ⊆ (interior (hdata.disk hselected.index))ᶜ := by
  intro z hzBoundary hzInterior
  exact
    selectedExteriorExcursionDisk_interior_subset_squareInterior
      (F := F) H hdata hselected hzInterior hzBoundary

/--
%%handwave
name:
  Selected exterior disk interiors are global exterior points
statement:
  The interior of the selected exterior-excursion disk is contained in the
  exterior preimage of the homotopy square.
-/
theorem selectedExteriorExcursionDisk_interior_subset_exteriorSet
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    interior (hdata.disk hselected.index) ⊆
      pathHomotopyExteriorSet (F := F) H := by
  intro z hz
  exact hselected.interior_maps_to_exterior hz

/--
%%handwave
name:
  Selected exterior disks are compact
statement:
  The selected exterior-excursion disk is compact.
proof:
  It is a closed parameter disk.
-/
theorem selectedExteriorExcursionDisk_isCompact
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    IsCompact (hdata.disk hselected.index) :=
  hselected.disk_closed.isCompact

/--
%%handwave
name:
  Selected exterior disks are closed
statement:
  The selected exterior-excursion disk is closed in the homotopy square.
proof:
  It is a compact subset of the Hausdorff parameter square.
-/
theorem selectedExteriorExcursionDisk_isClosed
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    IsClosed (hdata.disk hselected.index) :=
  hselected.disk_closed.isClosed

/--
%%handwave
name:
  Selected exterior disk frontiers lie in the square interior
statement:
  The frontier of the selected exterior-excursion disk lies away from the
  boundary of the homotopy square.
proof:
  The selected disk is closed, so its frontier is contained in the disk; the
  disk itself lies in the square interior.
-/
theorem selectedExteriorExcursionDisk_frontier_subset_squareInterior
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    frontier (hdata.disk hselected.index) ⊆ unitSquareBoundaryᶜ := by
  intro z hz
  have hz_closure : z ∈ closure (hdata.disk hselected.index) :=
    frontier_subset_closure hz
  have hz_disk : z ∈ hdata.disk hselected.index := by
    simpa [(selectedExteriorExcursionDisk_isClosed
      (F := F) H hdata hselected).closure_eq] using hz_closure
  exact
    selectedExteriorExcursionDisk_subset_squareInterior
      (F := F) H hdata hselected hz_disk

/--
%%handwave
name:
  Selected exterior disk has frontier on the smooth frontier
statement:
  The frontier of the selected exterior-excursion disk maps to the frontier
  of \(F\).
-/
theorem selectedExteriorExcursionDisk_frontier_maps_to_frontier
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    MapsTo H (frontier (hdata.disk hselected.index)) (frontier F) :=
  hselected.frontier_maps_to_frontier

/--
%%handwave
name:
  Selected exterior disk frontiers are global frontier-preimage points
statement:
  The frontier of the selected exterior-excursion disk is contained in the
  frontier preimage of the homotopy square.
-/
theorem selectedExteriorExcursionDisk_frontier_subset_frontierPreimage
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    frontier (hdata.disk hselected.index) ⊆
      pathHomotopyFrontierPreimage (F := F) H := by
  intro z hz
  exact hselected.frontier_maps_to_frontier hz

/--
%%handwave
name:
  Selected exterior disk frontiers are compact
statement:
  The frontier of the selected exterior-excursion disk is compact in the
  homotopy square.
proof:
  The selected disk is compact and closed; its frontier is a closed subset of
  it.
-/
theorem selectedExteriorExcursionDisk_frontier_isCompact
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    IsCompact (frontier (hdata.disk hselected.index)) := by
  have hcompact :
      IsCompact (hdata.disk hselected.index) :=
    selectedExteriorExcursionDisk_isCompact (F := F) H hdata hselected
  have hclosed :
      IsClosed (hdata.disk hselected.index) :=
    selectedExteriorExcursionDisk_isClosed (F := F) H hdata hselected
  refine hcompact.of_isClosed_subset isClosed_frontier ?_
  intro z hz
  have hzcl : z ∈ closure (hdata.disk hselected.index) :=
    frontier_subset_closure hz
  simpa [hclosed.closure_eq] using hzcl

/--
%%handwave
name:
  Selected exterior disk frontier images are compact
statement:
  The image of the selected disk frontier under the homotopy square is
  compact.
proof:
  The selected disk frontier is compact and the homotopy is continuous.
-/
theorem selectedExteriorExcursionDisk_frontierImage_isCompact
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    IsCompact (H '' frontier (hdata.disk hselected.index)) :=
  (selectedExteriorExcursionDisk_frontier_isCompact
    (F := F) H hdata hselected).image
      (ContinuousMap.HomotopyWith.continuous H)

/--
%%handwave
name:
  Selected exterior disk frontier images lie on the smooth frontier
statement:
  The image of the selected disk frontier lies in the frontier of \(F\).
-/
theorem selectedExteriorExcursionDisk_frontierImage_subset_frontier
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    H '' frontier (hdata.disk hselected.index) ⊆ frontier F := by
  rintro x ⟨z, hz, rfl⟩
  exact hselected.frontier_maps_to_frontier hz

/--
%%handwave
name:
  Selected exterior disk frontier images lie among the global frontier-hit values
statement:
  The image of the selected disk frontier is contained in the image of the
  global frontier preimage.
-/
theorem selectedExteriorExcursionDisk_frontierImage_subset_pathHomotopy_frontierImage
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    H '' frontier (hdata.disk hselected.index) ⊆
      H '' pathHomotopyFrontierPreimage (F := F) H := by
  rintro x ⟨z, hz, rfl⟩
  exact
    ⟨z,
      selectedExteriorExcursionDisk_frontier_subset_frontierPreimage
        (F := F) H hdata hselected hz,
      rfl⟩

/--
%%handwave
name:
  Selected exterior disk frontier images have finite smooth boundary-chart covers
statement:
  The image of the selected disk frontier is covered by finitely many smooth
  boundary charts of \(F\).
proof:
  The selected disk frontier image is compact and lies in the smooth frontier
  of \(F\), so compactness gives a finite subcover by local smooth boundary
  charts.
-/
theorem selectedExteriorExcursionDisk_frontierImage_finiteLocalBoundaryChartCover
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    ∃ t : Finset (H '' frontier (hdata.disk hselected.index)),
      H '' frontier (hdata.disk hselected.index) ⊆
        ⋃ x ∈ t,
          (smoothBoundary_localBoundaryChartData
            (F := F) hF_smooth (x : X)
            (selectedExteriorExcursionDisk_frontierImage_subset_frontier
              (F := F) H hdata hselected x.2)).neighborhood := by
  exact
    smoothBoundary_compactFrontierSubset_finiteLocalBoundaryChartCover
      (F := F) hF_smooth
      (selectedExteriorExcursionDisk_frontierImage_isCompact
        (F := F) H hdata hselected)
      (selectedExteriorExcursionDisk_frontierImage_subset_frontier
        (F := F) H hdata hselected)

/--
%%handwave
name:
  Empty exterior data
statement:
  If the exterior preimage of a homotopy square is empty, then it admits
  finite exterior-excursion data with no disks.
-/
def finiteExteriorExcursionData_empty
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hExterior_empty : pathHomotopyExteriorSet (F := F) H = ∅) :
    FiniteExteriorExcursionData (F := F) H where
  ι := Empty
  finite := inferInstance
  disk := Empty.elim
  disk_closed := by
    intro i
    exact Empty.elim i
  disk_regular := by
    intro i
    exact Empty.elim i
  disk_subset_interior := by
    intro i
    exact Empty.elim i
  exterior_eq := by
    simp [hExterior_empty]
  pairwise_disjoint_interiors := by
    intro i
    exact Empty.elim i
  interior_maps_to_exterior := by
    intro i
    exact Empty.elim i
  frontier_maps_to_frontier := by
    intro i
    exact Empty.elim i

/--
%%handwave
name:
  Finite boundary-chart general-position data
statement:
  Finite boundary-chart general-position data is a replacement homotopy
  between the original two paths, with boundary in \(F\), in finite
  exterior-excursion position.
-/
structure FiniteBoundaryChartGeneralPositionData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} (γ₀ γ₁ : Path a b) : Type 1 where
  position : FiniteExteriorExcursionPosition (F := F) γ₀ γ₁

/--
%%handwave
name:
  General-position data gives finite exterior-excursion position
statement:
  Finite boundary-chart general-position data immediately gives finite
  exterior-excursion position.
-/
theorem FiniteBoundaryChartGeneralPositionData.exists_position
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (hdata : FiniteBoundaryChartGeneralPositionData (F := F) γ₀ γ₁) :
    ∃ _hposition : FiniteExteriorExcursionPosition (F := F) γ₀ γ₁, True :=
  ⟨hdata.position, trivial⟩











/--
%%handwave
name:
  Empty finite exterior data has empty exterior set
statement:
  If the finite exterior-excursion data has no disks, then the part of the
  parameter square mapping outside \(\overline F\) is empty.
proof:
  The exterior set is the union of the interiors of the indexed disks, and an
  empty indexed union is empty.
-/
theorem finiteExteriorExcursionData_emptyIndex_exteriorSet_eq_empty
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    [IsEmpty hdata.ι] :
    pathHomotopyExteriorSet (F := F) H = ∅ := by
  rw [hdata.exterior_eq]
  simp

/--
%%handwave
name:
  Empty finite exterior data already gives a closure-valued homotopy
statement:
  If the finite exterior-excursion data has no disks, then the original
  homotopy already has image in \(\overline F\).
proof:
  The exterior set is empty, so every parameter point maps into
  \(\overline F\).
-/
theorem finiteExteriorExcursionData_emptyIndex_pathHomotopy_pushes_to_closure
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    [IsEmpty hdata.ι] :
    ∃ Hc : γ₀.Homotopy γ₁, ∀ z, Hc z ∈ closure F :=
  pathHomotopy_pushes_to_closure_of_exteriorSet_eq_empty
    (F := F) H
    (finiteExteriorExcursionData_emptyIndex_exteriorSet_eq_empty
      (F := F) H hdata)

/--
%%handwave
name:
  One-step finite exterior-excursion surgery data
statement:
  A one-step finite exterior-excursion surgery replaces a homotopy square by
  another homotopy between the same paths, still with boundary in \(F\), whose
  finite exterior-excursion data has strictly fewer disks.
-/
structure FiniteExteriorExcursionSurgeryStep
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H) : Type 1 where
  homotopy : γ₀.Homotopy γ₁
  boundary_mapsTo : ∀ z, z ∈ unitSquareBoundary → homotopy z ∈ F
  data : FiniteExteriorExcursionData (F := F) homotopy
  card_lt :
    finiteExteriorExcursionDataCard data <
      finiteExteriorExcursionDataCard hdata

/--
%%handwave
name:
  A one-step surgery result is a finite exterior-excursion position
statement:
  The replacement homotopy and finite data recorded by a one-step surgery
  result form a finite exterior-excursion position.
-/
def FiniteExteriorExcursionSurgeryStep.toPosition
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    (hstep : FiniteExteriorExcursionSurgeryStep (F := F) H hdata) :
    FiniteExteriorExcursionPosition (F := F) γ₀ γ₁ where
  homotopy := hstep.homotopy
  boundary_mapsTo := hstep.boundary_mapsTo
  data := hstep.data

/--
%%handwave
name:
  Remaining exterior-excursion trace after deleting a selected disk
statement:
  The remaining exterior trace is the union of the interiors of all old
  exterior-excursion disks except the selected one.
-/
def finiteExteriorExcursionRemainingSet
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Set (unitInterval × unitInterval) :=
  ⋃ j : {j : hdata.ι // j ≠ hselected.index},
    interior (hdata.disk (j : hdata.ι))

/--
%%handwave
name:
  Remaining exterior-excursion trace lies in the old exterior trace
statement:
  The union of the old exterior disks except the selected one is contained in
  the original exterior set.
proof:
  Each retained disk interior is one of the old exterior-excursion disk
  interiors, and the original exterior set is their union.
-/
theorem finiteExteriorExcursionRemainingSet_subset_exteriorSet
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    finiteExteriorExcursionRemainingSet hdata hselected ⊆
      pathHomotopyExteriorSet (F := F) H := by
  intro z hz
  rw [hdata.exterior_eq]
  change z ∈ ⋃ j : {j : hdata.ι // j ≠ hselected.index},
    interior (hdata.disk (j : hdata.ι)) at hz
  rcases mem_iUnion.mp hz with ⟨j, hzj⟩
  exact mem_iUnion_of_mem (j : hdata.ι) hzj

/--
%%handwave
name:
  Remaining exterior-excursion trace lies in the square interior
statement:
  After deleting a selected disk, the retained exterior-excursion trace still
  lies away from the boundary of the homotopy square.
proof:
  Each retained disk was already contained in the square interior.
-/
theorem finiteExteriorExcursionRemainingSet_subset_squareInterior
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    finiteExteriorExcursionRemainingSet hdata hselected ⊆ unitSquareBoundaryᶜ := by
  intro z hz
  change z ∈ ⋃ j : {j : hdata.ι // j ≠ hselected.index},
    interior (hdata.disk (j : hdata.ι)) at hz
  rcases mem_iUnion.mp hz with ⟨j, hzj⟩
  exact hdata.disk_subset_interior (j : hdata.ι) (interior_subset hzj)

/--
%%handwave
name:
  The retained exterior-excursion trace is open
statement:
  The union of the retained old exterior-disk interiors is open.
proof:
  It is a union of open interiors.
-/
theorem finiteExteriorExcursionRemainingSet_isOpen
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    IsOpen (finiteExteriorExcursionRemainingSet hdata hselected) := by
  dsimp [finiteExteriorExcursionRemainingSet]
  exact isOpen_iUnion fun _j => isOpen_interior

/--
%%handwave
name:
  The retained trace is disjoint from the selected disk interior
statement:
  The retained exterior-disk interiors are disjoint from the selected
  exterior-disk interior.
proof:
  This is the pairwise disjointness of the old finite exterior-excursion
  disk interiors.
-/
theorem finiteExteriorExcursionRemainingSet_disjoint_selectedInterior
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Disjoint (finiteExteriorExcursionRemainingSet hdata hselected)
      (interior (hdata.disk hselected.index)) := by
  rw [Set.disjoint_left]
  intro z hz_remaining hz_selected
  change z ∈ ⋃ j : {j : hdata.ι // j ≠ hselected.index},
    interior (hdata.disk (j : hdata.ι)) at hz_remaining
  rcases mem_iUnion.mp hz_remaining with ⟨j, hzj⟩
  have hdisj :
      Disjoint (interior (hdata.disk (j : hdata.ι)))
        (interior (hdata.disk hselected.index)) :=
    hdata.pairwise_disjoint_interiors j.2
  rw [Set.disjoint_left] at hdisj
  exact hdisj hzj hz_selected

/--
%%handwave
name:
  The retained trace avoids the selected disk interior
statement:
  The retained exterior-excursion trace is contained in the complement of the
  selected disk interior.
proof:
  This is the same disjointness statement, read as a containment in the
  complement.
-/
theorem finiteExteriorExcursionRemainingSet_subset_compl_selectedInterior
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    finiteExteriorExcursionRemainingSet hdata hselected ⊆
      (interior (hdata.disk hselected.index))ᶜ := by
  intro z hz_remaining hz_selected
  have hdisj :
      Disjoint (finiteExteriorExcursionRemainingSet hdata hselected)
        (interior (hdata.disk hselected.index)) :=
    finiteExteriorExcursionRemainingSet_disjoint_selectedInterior
      (F := F) hdata hselected
  rw [Set.disjoint_left] at hdisj
  exact hdisj hz_remaining hz_selected

/--
%%handwave
name:
  Each retained disk interior avoids the selected disk interior
statement:
  The interior of every nonselected exterior-excursion disk is contained in
  the complement of the selected disk interior.
proof:
  This is the pairwise disjointness of the recorded disk interiors.
-/
theorem retainedExteriorExcursionDisk_interior_subset_compl_selectedInterior
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (j : {j : hdata.ι // j ≠ hselected.index}) :
    interior (hdata.disk (j : hdata.ι)) ⊆
      (interior (hdata.disk hselected.index))ᶜ := by
  intro z hzj hzselected
  have hdisj :
      Disjoint (interior (hdata.disk (j : hdata.ι)))
        (interior (hdata.disk hselected.index)) :=
    hdata.pairwise_disjoint_interiors j.2
  rw [Set.disjoint_left] at hdisj
  exact hdisj hzj hzselected

/--
%%handwave
name:
  Retained exterior-excursion frontiers
statement:
  The retained exterior-excursion frontier set is the union of the frontiers
  of all old exterior-excursion disks except the selected one.
-/
def finiteExteriorExcursionRetainedFrontierSet
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Set (unitInterval × unitInterval) :=
  ⋃ j : {j : hdata.ι // j ≠ hselected.index},
    frontier (hdata.disk (j : hdata.ι))

/--
%%handwave
name:
  Each retained frontier lies in the retained frontier set
statement:
  The frontier of every nonselected exterior-excursion disk is contained in
  the retained frontier set.
-/
theorem retainedExteriorExcursionDisk_frontier_subset_retainedFrontierSet
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (j : {j : hdata.ι // j ≠ hselected.index}) :
    frontier (hdata.disk (j : hdata.ι)) ⊆
      finiteExteriorExcursionRetainedFrontierSet hdata hselected := by
  intro z hz
  change z ∈ ⋃ j : {j : hdata.ι // j ≠ hselected.index},
    frontier (hdata.disk (j : hdata.ι))
  exact mem_iUnion_of_mem j hz

/--
%%handwave
name:
  Retained frontiers map to the frontier
statement:
  The retained exterior-excursion frontier set maps to the frontier of \(F\)
  under the original homotopy square.
proof:
  Each retained frontier is one of the recorded disk frontiers in the finite
  exterior-excursion data.
-/
theorem finiteExteriorExcursionRetainedFrontierSet_mapsTo_frontier
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    MapsTo H
      (finiteExteriorExcursionRetainedFrontierSet hdata hselected)
      (frontier F) := by
  intro z hz
  change z ∈ ⋃ j : {j : hdata.ι // j ≠ hselected.index},
    frontier (hdata.disk (j : hdata.ι)) at hz
  rcases mem_iUnion.mp hz with ⟨j, hzj⟩
  exact hdata.frontier_maps_to_frontier (j : hdata.ι) hzj

/--
%%handwave
name:
  Retained frontiers map to the closure
statement:
  The retained exterior-excursion frontier set maps to \(\overline F\) under
  the original homotopy square.
proof:
  Retained frontiers map to the frontier of \(F\), and the frontier lies in
  \(\overline F\).
-/
theorem finiteExteriorExcursionRetainedFrontierSet_mapsTo_closure
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    MapsTo H
      (finiteExteriorExcursionRetainedFrontierSet hdata hselected)
      (closure F) := by
  intro z hz
  exact frontier_subset_closure
    (finiteExteriorExcursionRetainedFrontierSet_mapsTo_frontier
      (F := F) hdata hselected hz)

/--
%%handwave
name:
  Retained frontiers form a closed set
statement:
  The union of the retained exterior-excursion frontiers is closed in the
  parameter square.
proof:
  There are only finitely many retained disks, and each disk frontier is
  closed.
-/
theorem finiteExteriorExcursionRetainedFrontierSet_isClosed
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    IsClosed (finiteExteriorExcursionRetainedFrontierSet hdata hselected) := by
  classical
  letI : Fintype hdata.ι := hdata.finite
  rw [finiteExteriorExcursionRetainedFrontierSet]
  exact isClosed_iUnion_of_finite fun _ => isClosed_frontier

/--
%%handwave
name:
  Selected exterior-excursion patch region
statement:
  The protected patch region is the selected exterior-disk interior with all
  retained exterior-disk frontiers removed.
-/
def selectedExteriorExcursionPatchRegion
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Set (unitInterval × unitInterval) :=
  interior (hdata.disk hselected.index) \
    finiteExteriorExcursionRetainedFrontierSet hdata hselected

/--
%%handwave
name:
  Safe frontier for a selected exterior excursion
statement:
  The safe frontier for patching a selected exterior disk is the union of the
  selected disk frontier and the retained exterior-disk frontiers.
-/
def selectedExteriorExcursionSafeFrontierSet
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Set (unitInterval × unitInterval) :=
  frontier (hdata.disk hselected.index) ∪
    finiteExteriorExcursionRetainedFrontierSet hdata hselected

/--
%%handwave
name:
  Safe frontier maps to the frontier
statement:
  The safe frontier for a selected exterior excursion maps to the frontier of
  \(F\) under the original homotopy square.
proof:
  The selected frontier maps to the frontier by the selected-disk data, and
  the retained frontiers do so by the retained-frontier lemma.
-/
theorem selectedExteriorExcursionSafeFrontierSet_mapsTo_frontier
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    MapsTo H
      (selectedExteriorExcursionSafeFrontierSet hdata hselected)
      (frontier F) := by
  intro z hz
  rcases hz with hzSelected | hzRetained
  · exact selectedExteriorExcursionDisk_frontier_maps_to_frontier
      (F := F) H hdata hselected hzSelected
  · exact finiteExteriorExcursionRetainedFrontierSet_mapsTo_frontier
      (F := F) hdata hselected hzRetained

/--
%%handwave
name:
  Safe frontier maps to the closure
statement:
  The safe frontier for a selected exterior excursion maps to \(\overline F\)
  under the original homotopy square.
proof:
  It maps to the frontier, and the frontier is contained in the closure.
-/
theorem selectedExteriorExcursionSafeFrontierSet_mapsTo_closure
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    MapsTo H
      (selectedExteriorExcursionSafeFrontierSet hdata hselected)
      (closure F) := by
  intro z hz
  exact frontier_subset_closure
    (selectedExteriorExcursionSafeFrontierSet_mapsTo_frontier
      (F := F) hdata hselected hz)

/--
%%handwave
name:
  The safe frontier is closed
statement:
  The safe frontier for patching a selected exterior excursion is closed in
  the parameter square.
proof:
  It is the union of the selected disk frontier and the finite union of the
  retained disk frontiers.
-/
theorem selectedExteriorExcursionSafeFrontierSet_isClosed
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    IsClosed (selectedExteriorExcursionSafeFrontierSet hdata hselected) := by
  exact isClosed_frontier.union
    (finiteExteriorExcursionRetainedFrontierSet_isClosed
      (F := F) hdata hselected)

/--
%%handwave
name:
  The retained trace lies in the old exterior trace minus the selected disk
statement:
  The retained exterior trace is contained in the original exterior trace
  with the selected disk interior removed.
proof:
  It lies in the old exterior trace and is disjoint from the selected disk
  interior.
-/
theorem finiteExteriorExcursionRemainingSet_subset_exteriorSet_diff_selectedInterior
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    finiteExteriorExcursionRemainingSet hdata hselected ⊆
      pathHomotopyExteriorSet (F := F) H \
        interior (hdata.disk hselected.index) := by
  intro z hz_remaining
  refine
    ⟨finiteExteriorExcursionRemainingSet_subset_exteriorSet
        (F := F) hdata hselected hz_remaining, ?_⟩
  have hdisj :
      Disjoint (finiteExteriorExcursionRemainingSet hdata hselected)
        (interior (hdata.disk hselected.index)) :=
    finiteExteriorExcursionRemainingSet_disjoint_selectedInterior
      (F := F) hdata hselected
  rw [Set.disjoint_left] at hdisj
  exact hdisj hz_remaining

/--
%%handwave
name:
  Removing the selected interior from the old exterior trace leaves the
  retained trace
statement:
  The original exterior trace with the selected disk interior removed is
  contained in the retained exterior trace.
proof:
  The old exterior trace is the union of all old disk interiors.  A point
  outside the selected interior must belong to one of the nonselected disk
  interiors.
-/
theorem exteriorSet_diff_selectedInterior_subset_finiteExteriorExcursionRemainingSet
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    pathHomotopyExteriorSet (F := F) H \
        interior (hdata.disk hselected.index) ⊆
      finiteExteriorExcursionRemainingSet hdata hselected := by
  intro z hz
  rcases hz with ⟨hz_exterior, hz_not_selected⟩
  rw [hdata.exterior_eq] at hz_exterior
  rcases mem_iUnion.mp hz_exterior with ⟨i, hzi⟩
  by_cases hi : i = hselected.index
  · exact False.elim (hz_not_selected (by simpa [hi] using hzi))
  · change z ∈ ⋃ j : {j : hdata.ι // j ≠ hselected.index},
      interior (hdata.disk (j : hdata.ι))
    exact mem_iUnion_of_mem ⟨i, hi⟩ hzi

/--
%%handwave
name:
  The retained exterior trace is old exterior minus the selected interior
statement:
  The retained exterior-excursion trace is exactly the original exterior
  trace after deleting the selected disk interior.
proof:
  One inclusion uses pairwise disjointness from the selected disk; the other
  unfolds the old exterior trace as the union of all old disk interiors.
-/
theorem exteriorSet_diff_selectedInterior_eq_finiteExteriorExcursionRemainingSet
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    pathHomotopyExteriorSet (F := F) H \
        interior (hdata.disk hselected.index) =
      finiteExteriorExcursionRemainingSet hdata hselected :=
  subset_antisymm
    (exteriorSet_diff_selectedInterior_subset_finiteExteriorExcursionRemainingSet
      (F := F) hdata hselected)
    (finiteExteriorExcursionRemainingSet_subset_exteriorSet_diff_selectedInterior
      (F := F) hdata hselected)

/--
%%handwave
name:
  Core selected exterior-disk surgery homotopy data
statement:
  Core surgery data for deleting a selected exterior disk is a replacement
  homotopy with boundary still in \(F\), whose exterior trace is exactly the
  retained old exterior disks, and which agrees with the old homotopy on the
  retained disk interiors and frontiers.
-/
structure SelectedExteriorExcursionSurgeryHomotopyCoreData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Type 1 where
  homotopy : γ₀.Homotopy γ₁
  boundary_mapsTo : ∀ z, z ∈ unitSquareBoundary → homotopy z ∈ F
  exterior_eq_remaining :
    pathHomotopyExteriorSet (F := F) homotopy =
      finiteExteriorExcursionRemainingSet hdata hselected
  eqOn_remaining_interiors :
    ∀ j : {j : hdata.ι // j ≠ hselected.index},
      EqOn homotopy H (interior (hdata.disk (j : hdata.ι)))
  eqOn_remaining_frontiers :
    ∀ j : {j : hdata.ι // j ≠ hselected.index},
      EqOn homotopy H (frontier (hdata.disk (j : hdata.ι)))

/--
%%handwave
name:
  Trace-level selected exterior-disk surgery data
statement:
  Trace-level selected-disk surgery data is a replacement homotopy whose
  exterior trace is the old exterior trace with the selected disk interior
  deleted, and which agrees with the old homotopy on the retained disk
  interiors and frontiers.
-/
structure SelectedExteriorExcursionTraceSurgeryData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Type 1 where
  homotopy : γ₀.Homotopy γ₁
  boundary_mapsTo : ∀ z, z ∈ unitSquareBoundary → homotopy z ∈ F
  exterior_eq_old_diff_selected :
    pathHomotopyExteriorSet (F := F) homotopy =
      pathHomotopyExteriorSet (F := F) H \
        interior (hdata.disk hselected.index)
  eqOn_remaining_interiors :
    ∀ j : {j : hdata.ι // j ≠ hselected.index},
      EqOn homotopy H (interior (hdata.disk (j : hdata.ι)))
  eqOn_remaining_frontiers :
    ∀ j : {j : hdata.ι // j ≠ hselected.index},
      EqOn homotopy H (frontier (hdata.disk (j : hdata.ι)))

/--
%%handwave
name:
  Closure patch data for a selected exterior disk
statement:
  Closure patch data for a selected exterior disk is a replacement homotopy
  that is unchanged off the selected disk interior, sends the selected disk
  interior into \(\overline F\), and is unchanged on the retained disk
  frontiers.
-/
structure SelectedExteriorExcursionClosurePatchData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Type 1 where
  homotopy : γ₀.Homotopy γ₁
  selectedInterior_mapsTo_closure :
    MapsTo homotopy (interior (hdata.disk hselected.index)) (closure F)
  eqOn_off_selectedInterior :
    EqOn homotopy H (interior (hdata.disk hselected.index))ᶜ
  eqOn_remaining_frontiers :
    ∀ j : {j : hdata.ι // j ≠ hselected.index},
      EqOn homotopy H (frontier (hdata.disk (j : hdata.ι)))

/--
%%handwave
name:
  Closure patch map data for a selected exterior disk
statement:
  Map-level closure patch data for a selected exterior disk is a continuous
  replacement square with the same two path sides and fixed endpoints, which
  sends the selected disk interior into \(\overline F\), is unchanged off the
  selected disk interior, and is unchanged on the retained disk frontiers.
-/
structure SelectedExteriorExcursionClosurePatchMapData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Type 1 where
  map : C(unitInterval × unitInterval, X)
  source_path : ∀ s : unitInterval, map (0, s) = γ₀ s
  target_path : ∀ s : unitInterval, map (1, s) = γ₁ s
  left_endpoint : ∀ t : unitInterval, map (t, 0) = a
  right_endpoint : ∀ t : unitInterval, map (t, 1) = b
  selectedInterior_mapsTo_closure :
    MapsTo map (interior (hdata.disk hselected.index)) (closure F)
  eqOn_off_selectedInterior :
    EqOn map H (interior (hdata.disk hselected.index))ᶜ
  eqOn_remaining_frontiers :
    ∀ j : {j : hdata.ι // j ≠ hselected.index},
      EqOn map H (frontier (hdata.disk (j : hdata.ι)))

/--
%%handwave
name:
  Supported closure patch square data for a selected exterior disk
statement:
  Supported closure patch square data for a selected exterior disk is a
  continuous replacement square that sends the selected disk interior into
  \(\overline F\), is unchanged off the selected disk interior, and is
  unchanged on the retained disk frontiers.
-/
structure SelectedExteriorExcursionClosurePatchSupportedMapData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Type 1 where
  map : C(unitInterval × unitInterval, X)
  selectedInterior_mapsTo_closure :
    MapsTo map (interior (hdata.disk hselected.index)) (closure F)
  eqOn_off_selectedInterior :
    EqOn map H (interior (hdata.disk hselected.index))ᶜ
  eqOn_remaining_frontiers :
    ∀ j : {j : hdata.ι // j ≠ hselected.index},
      EqOn map H (frontier (hdata.disk (j : hdata.ι)))

/--
%%handwave
name:
  Selected exterior disk closure-filling data
statement:
  Closure-filling data for a selected exterior disk is a continuous map on
  the selected closed parameter disk whose image lies in \(\overline F\), and
  which agrees with the old homotopy on the selected frontier and on every
  retained frontier point lying in the selected disk.
-/
structure SelectedExteriorExcursionDiskClosureFillingData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Type 1 where
  filling : C(hdata.disk hselected.index, X)
  filling_mapsTo_closure :
    MapsTo filling univ (closure F)
  eqOn_selected_frontier :
    ∀ ⦃z : unitInterval × unitInterval⦄ (hzDisk : z ∈ hdata.disk hselected.index),
      z ∈ frontier (hdata.disk hselected.index) →
        filling ⟨z, hzDisk⟩ = H z
  eqOn_retained_frontiers :
    ∀ j : {j : hdata.ι // j ≠ hselected.index},
      ∀ ⦃z : unitInterval × unitInterval⦄
        (hzDisk : z ∈ hdata.disk hselected.index),
        z ∈ frontier (hdata.disk (j : hdata.ι)) →
          filling ⟨z, hzDisk⟩ = H z

/--
%%handwave
name:
  Protected trace on a selected exterior disk
statement:
  The protected trace on the selected closed parameter disk consists of the
  selected disk frontier together with all retained exterior-disk frontiers
  that meet the selected disk.
-/
def selectedExteriorExcursionDiskProtectedTraceSet
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Set (hdata.disk hselected.index) :=
  {z | (z : unitInterval × unitInterval) ∈
        frontier (hdata.disk hselected.index) ∨
      (z : unitInterval × unitInterval) ∈
        finiteExteriorExcursionRetainedFrontierSet hdata hselected}

/--
%%handwave
name:
  The protected trace is closed in the selected disk
statement:
  The protected trace on the selected closed parameter disk is closed as a
  subset of that disk.
proof:
  It is the inverse image of the closed safe frontier under the inclusion of
  the selected disk into the parameter square.
-/
theorem selectedExteriorExcursionDiskProtectedTraceSet_isClosed
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    IsClosed (selectedExteriorExcursionDiskProtectedTraceSet hdata hselected) := by
  let safe : Set (unitInterval × unitInterval) :=
    selectedExteriorExcursionSafeFrontierSet hdata hselected
  have hsafe : IsClosed safe := by
    simpa [safe] using
      selectedExteriorExcursionSafeFrontierSet_isClosed
        (F := F) hdata hselected
  have hpre :
      selectedExteriorExcursionDiskProtectedTraceSet hdata hselected =
        (fun z : hdata.disk hselected.index =>
          (z : unitInterval × unitInterval)) ⁻¹' safe := by
    ext z
    rfl
  rw [hpre]
  exact hsafe.preimage continuous_subtype_val

/--
%%handwave
name:
  The protected trace is compact
statement:
  The protected trace on the selected closed parameter disk is compact.
proof:
  The selected parameter disk is compact, and the protected trace is closed
  in it.
-/
theorem selectedExteriorExcursionDiskProtectedTraceSet_isCompact
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    IsCompact (selectedExteriorExcursionDiskProtectedTraceSet hdata hselected) := by
  haveI : CompactSpace (hdata.disk hselected.index) :=
    isCompact_iff_compactSpace.mp
      (selectedExteriorExcursionDisk_isCompact (F := F) H hdata hselected)
  exact
    (selectedExteriorExcursionDiskProtectedTraceSet_isClosed
      (F := F) hdata hselected).isCompact

/--
%%handwave
name:
  The protected trace is nonempty
statement:
  The protected trace of a selected regular closed parameter disk is
  nonempty.
proof:
  The selected disk frontier is a circle, hence has a point.  Since the
  selected disk is closed, this frontier point belongs to the selected
  closed disk, and it lies in the protected trace by definition.
-/
theorem selectedExteriorExcursionDiskProtectedTraceSet_nonempty
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    (selectedExteriorExcursionDiskProtectedTraceSet hdata hselected).Nonempty := by
  rcases hselected.disk_regular.frontier_homeomorph_circle with ⟨e⟩
  let w : Metric.sphere (0 : ℂ) 1 :=
    ⟨(1 : ℂ), by simp⟩
  let y : frontier (hdata.disk hselected.index) := e.symm w
  have hy_disk :
      (y : unitInterval × unitInterval) ∈ hdata.disk hselected.index := by
    have hy_closure :
        (y : unitInterval × unitInterval) ∈
          closure (hdata.disk hselected.index) :=
      frontier_subset_closure y.2
    simpa [(selectedExteriorExcursionDisk_isClosed
      (F := F) H hdata hselected).closure_eq] using hy_closure
  refine ⟨⟨(y : unitInterval × unitInterval), hy_disk⟩, ?_⟩
  exact Or.inl y.2

/--
%%handwave
name:
  The protected trace maps to the frontier
statement:
  On the protected trace of a selected exterior disk, the old homotopy takes
  values on the frontier of \(F\).
proof:
  The selected disk frontier maps to the frontier by the selected-disk data,
  and every retained frontier maps to the frontier by the finite
  exterior-excursion data.
-/
theorem selectedExteriorExcursionDiskProtectedTraceSet_mapsTo_frontier
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    MapsTo
      (fun z : hdata.disk hselected.index =>
        H (z : unitInterval × unitInterval))
      (selectedExteriorExcursionDiskProtectedTraceSet hdata hselected)
      (frontier F) := by
  intro z hz
  change
    (z : unitInterval × unitInterval) ∈
        frontier (hdata.disk hselected.index) ∨
      (z : unitInterval × unitInterval) ∈
        finiteExteriorExcursionRetainedFrontierSet hdata hselected at hz
  rcases hz with hzSelected | hzRetained
  · exact selectedExteriorExcursionDisk_frontier_maps_to_frontier
      (F := F) H hdata hselected hzSelected
  · exact finiteExteriorExcursionRetainedFrontierSet_mapsTo_frontier
      (F := F) hdata hselected hzRetained

/--
%%handwave
name:
  Image of the protected trace
statement:
  The protected trace image is the image of the protected trace under the old
  homotopy.
-/
def selectedExteriorExcursionDiskProtectedTraceImage
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Set X :=
  (fun z : hdata.disk hselected.index =>
    H (z : unitInterval × unitInterval)) ''
      selectedExteriorExcursionDiskProtectedTraceSet hdata hselected

/--
%%handwave
name:
  The protected trace image is compact
statement:
  If the protected trace is compact, then its image under the old homotopy is
  compact.
proof:
  The old homotopy is continuous, and the inclusion of the selected disk into
  the parameter square is continuous.
-/
theorem selectedExteriorExcursionDiskProtectedTraceImage_isCompact_of_isCompact
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (hprotected_compact :
      IsCompact (selectedExteriorExcursionDiskProtectedTraceSet hdata hselected)) :
    IsCompact
      (selectedExteriorExcursionDiskProtectedTraceImage
        (F := F) H hdata hselected) := by
  simpa [selectedExteriorExcursionDiskProtectedTraceImage] using
    hprotected_compact.image
      ((ContinuousMap.HomotopyWith.continuous H).comp continuous_subtype_val)

/--
%%handwave
name:
  The protected trace image is compact
statement:
  The image of the protected trace under the old homotopy is compact.
proof:
  The protected trace is compact and the old homotopy is continuous.
-/
theorem selectedExteriorExcursionDiskProtectedTraceImage_isCompact
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    IsCompact
      (selectedExteriorExcursionDiskProtectedTraceImage
        (F := F) H hdata hselected) :=
  selectedExteriorExcursionDiskProtectedTraceImage_isCompact_of_isCompact
    (F := F) hdata hselected
    (selectedExteriorExcursionDiskProtectedTraceSet_isCompact
      (F := F) hdata hselected)

/--
%%handwave
name:
  The protected trace image lies on the frontier
statement:
  The protected trace image is contained in the frontier of \(F\).
proof:
  Every protected trace point maps to the frontier.
-/
theorem selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    selectedExteriorExcursionDiskProtectedTraceImage
        (F := F) H hdata hselected ⊆ frontier F := by
  rintro x ⟨z, hz, rfl⟩
  exact
    selectedExteriorExcursionDiskProtectedTraceSet_mapsTo_frontier
      (F := F) hdata hselected hz

/--
%%handwave
name:
  Protected trace images have finite smooth boundary-chart covers
statement:
  If the protected trace is compact, then its image is covered by finitely
  many smooth boundary charts of \(F\).
proof:
  The protected trace image is compact and lies in the smooth frontier of
  \(F\), so compactness gives a finite subcover by local smooth boundary
  charts.
-/
theorem selectedExteriorExcursionDiskProtectedTraceImage_finiteLocalBoundaryChartCover_of_isCompact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (hprotected_compact :
      IsCompact (selectedExteriorExcursionDiskProtectedTraceSet hdata hselected)) :
    ∃ t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected),
      selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected ⊆
        ⋃ x ∈ t,
          (smoothBoundary_localBoundaryChartData
            (F := F) hF_smooth (x : X)
            (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
              (F := F) hdata hselected x.2)).neighborhood := by
  exact
    smoothBoundary_compactFrontierSubset_finiteLocalBoundaryChartCover
      (F := F) hF_smooth
      (selectedExteriorExcursionDiskProtectedTraceImage_isCompact_of_isCompact
        (F := F) hdata hselected hprotected_compact)
      (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
        (F := F) hdata hselected)

/--
%%handwave
name:
  Protected trace images have finite smooth boundary-chart covers
statement:
  The protected trace image is covered by finitely many smooth boundary
  charts of \(F\).
proof:
  Apply compactness of the protected trace image.
-/
theorem selectedExteriorExcursionDiskProtectedTraceImage_finiteLocalBoundaryChartCover
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    ∃ t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected),
      selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected ⊆
        ⋃ x ∈ t,
          (smoothBoundary_localBoundaryChartData
            (F := F) hF_smooth (x : X)
            (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
              (F := F) hdata hselected x.2)).neighborhood := by
  exact
    selectedExteriorExcursionDiskProtectedTraceImage_finiteLocalBoundaryChartCover_of_isCompact
      (F := F) hF_smooth hdata hselected
      (selectedExteriorExcursionDiskProtectedTraceSet_isCompact
        (F := F) hdata hselected)

/--
%%handwave
name:
  Protected trace chart covers are pointwise
statement:
  If finitely many smooth boundary charts cover the protected trace image,
  then every protected trace parameter maps into one of those chart
  neighborhoods.
proof:
  The image point of a protected trace parameter belongs to the protected
  trace image, so the finite cover supplies a chart containing it.
-/
theorem selectedExteriorExcursionDiskProtectedTrace_mem_chartCover
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected))
    (hprotectedTraceChartCover :
      selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected ⊆
        ⋃ x ∈ t,
          (smoothBoundary_localBoundaryChartData
            (F := F) hF_smooth (x : X)
            (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
              (F := F) hdata hselected x.2)).neighborhood)
    (z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected) :
    ∃ x :
      selectedExteriorExcursionDiskProtectedTraceImage
        (F := F) H hdata hselected,
      x ∈ t ∧
        H (z : unitInterval × unitInterval) ∈
          (smoothBoundary_localBoundaryChartData
            (F := F) hF_smooth (x : X)
            (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
              (F := F) hdata hselected x.2)).neighborhood := by
  have hzImage :
      H (z : unitInterval × unitInterval) ∈
        selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected := by
    exact ⟨(z : hdata.disk hselected.index), z.2, rfl⟩
  have hzCover :=
    hprotectedTraceChartCover hzImage
  simp only [mem_iUnion] at hzCover
  rcases hzCover with ⟨x, hx⟩
  rcases hx with ⟨hxt, hxmem⟩
  exact ⟨x, hxt, hxmem⟩

/--
%%handwave
name:
  The protected trace lands in the chart cover
statement:
  If finitely many smooth boundary charts cover the protected trace image,
  then the old homotopy on the protected trace lands in the union of those
  chart neighborhoods.
proof:
  This is the pointwise form of the chart-cover property.
-/
theorem selectedExteriorExcursionDiskProtectedTrace_mapsTo_chartCover
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected))
    (hprotectedTraceChartCover :
      selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected ⊆
        ⋃ x ∈ t,
          (smoothBoundary_localBoundaryChartData
            (F := F) hF_smooth (x : X)
            (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
              (F := F) hdata hselected x.2)).neighborhood) :
    MapsTo
      (fun z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected =>
        H (z : unitInterval × unitInterval))
      univ
      (⋃ x ∈ t,
        (smoothBoundary_localBoundaryChartData
          (F := F) hF_smooth (x : X)
          (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
            (F := F) hdata hselected x.2)).neighborhood) := by
  intro z _hz
  rcases
      selectedExteriorExcursionDiskProtectedTrace_mem_chartCover
        (F := F) hF_smooth hdata hselected t hprotectedTraceChartCover z with
    ⟨x, hxt, hxmem⟩
  simp only [mem_iUnion]
  exact ⟨x, hxt, by simpa using hxmem⟩

/--
%%handwave
name:
  The protected trace maps into the closure
statement:
  On the protected trace of a selected exterior disk, the old homotopy takes
  values in \(\overline F\).
proof:
  The selected frontier and all retained frontiers map to the frontier of
  \(F\), hence to \(\overline F\).
-/
theorem selectedExteriorExcursionDiskProtectedTraceSet_mapsTo_closure
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    MapsTo
      (fun z : hdata.disk hselected.index =>
        H (z : unitInterval × unitInterval))
      (selectedExteriorExcursionDiskProtectedTraceSet hdata hselected)
      (closure F) := by
  intro z hz
  exact frontier_subset_closure
    (selectedExteriorExcursionDiskProtectedTraceSet_mapsTo_frontier
      (F := F) hdata hselected hz)

/--
%%handwave
name:
  Protected trace as a frontier-valued map
statement:
  The old homotopy restricted to the protected trace of a selected exterior
  disk is a continuous map into the frontier of \(F\).
-/
def selectedExteriorExcursionDiskProtectedTraceFrontierMap
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
      frontier F) where
  toFun := fun z =>
    ⟨H ((z : hdata.disk hselected.index) : unitInterval × unitInterval),
      by
        have hmaps :=
          selectedExteriorExcursionDiskProtectedTraceSet_mapsTo_frontier
            (F := F) hdata hselected
        exact hmaps z.2⟩
  continuous_toFun := by
    exact Continuous.subtype_mk
      ((ContinuousMap.HomotopyWith.continuous H).comp
        (continuous_subtype_val.comp continuous_subtype_val))
      _

/--
%%handwave
name:
  Values of the frontier-valued protected trace map
statement:
  After forgetting the codomain restriction to the frontier, the
  frontier-valued protected trace map is just the original homotopy on the
  protected trace.
proof:
  This is immediate from the definition of the restricted map.
-/
@[simp] theorem selectedExteriorExcursionDiskProtectedTraceFrontierMap_coe
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected) :
    (selectedExteriorExcursionDiskProtectedTraceFrontierMap
      (F := F) H hdata hselected z : X) =
      H (z : unitInterval × unitInterval) := by
  rfl

/--
%%handwave
name:
  The frontier-valued protected trace map lands in the chart cover
statement:
  If finitely many smooth boundary charts cover the protected trace image,
  then the frontier-valued protected trace map lands, after forgetting to the
  ambient surface, in the union of those chart neighborhoods.
proof:
  The frontier-valued trace map has the same ambient values as the original
  homotopy on the protected trace.
-/
theorem selectedExteriorExcursionDiskProtectedTraceFrontierMap_mapsTo_chartCover
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected))
    (hprotectedTraceChartCover :
      selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected ⊆
        ⋃ x ∈ t,
          (smoothBoundary_localBoundaryChartData
            (F := F) hF_smooth (x : X)
            (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
              (F := F) hdata hselected x.2)).neighborhood) :
    MapsTo
      (fun z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected =>
        (selectedExteriorExcursionDiskProtectedTraceFrontierMap
          (F := F) H hdata hselected z : X))
      univ
      (⋃ x ∈ t,
        (smoothBoundary_localBoundaryChartData
          (F := F) hF_smooth (x : X)
          (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
            (F := F) hdata hselected x.2)).neighborhood) := by
  intro z hz
  have hmaps :=
    selectedExteriorExcursionDiskProtectedTrace_mapsTo_chartCover
      (F := F) hF_smooth hdata hselected t hprotectedTraceChartCover
  simpa [selectedExteriorExcursionDiskProtectedTraceFrontierMap_coe] using
    hmaps (mem_univ z)

/--
%%handwave
name:
  Protected trace as a closure-valued map
statement:
  The old homotopy restricted to the protected trace of a selected exterior
  disk is a continuous map into \(\overline F\).
-/
def selectedExteriorExcursionDiskProtectedTraceMap
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
      closure F) where
  toFun := fun z =>
    ⟨H ((z : hdata.disk hselected.index) : unitInterval × unitInterval),
      by
        have hmaps :=
          selectedExteriorExcursionDiskProtectedTraceSet_mapsTo_closure
            (F := F) hdata hselected
        exact hmaps z.2⟩
  continuous_toFun := by
    exact Continuous.subtype_mk
      ((ContinuousMap.HomotopyWith.continuous H).comp
        (continuous_subtype_val.comp continuous_subtype_val))
      _

/--
%%handwave
name:
  Values of the protected trace map
statement:
  After forgetting the codomain restriction to \(\overline F\), the protected
  trace map is just the original homotopy on the protected trace.
proof:
  This is immediate from the definition of the restricted map.
-/
@[simp] theorem selectedExteriorExcursionDiskProtectedTraceMap_coe
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected) :
    (selectedExteriorExcursionDiskProtectedTraceMap (F := F) H hdata hselected z : X) =
      H (z : unitInterval × unitInterval) := by
  rfl

/--
%%handwave
name:
  Frontier and closure trace maps agree
statement:
  The frontier-valued protected trace map, followed by the inclusion
  \(\partial F\subset\overline F\), is the closure-valued protected trace
  map.
proof:
  Both maps have the same underlying ambient value at every protected trace
  point.
-/
@[simp] theorem
    selectedExteriorExcursionDiskProtectedTraceFrontierMap_toClosure_eq_traceMap
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected) :
    (⟨(selectedExteriorExcursionDiskProtectedTraceFrontierMap
          (F := F) H hdata hselected z : X),
        frontier_subset_closure
          (selectedExteriorExcursionDiskProtectedTraceFrontierMap
            (F := F) H hdata hselected z).2⟩ : closure F) =
      selectedExteriorExcursionDiskProtectedTraceMap
        (F := F) H hdata hselected z := by
  apply Subtype.ext
  rfl

/--
%%handwave
name:
  Protected trace extension data for a selected exterior disk
statement:
  Protected trace extension data is a continuous map from the selected closed
  parameter disk to \(\overline F\) that restricts to the old homotopy on the
  selected frontier and retained-frontier trace.
-/
structure SelectedExteriorExcursionDiskProtectedTraceExtensionData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Type 1 where
  filling : C(hdata.disk hselected.index, closure F)
  eqOn_protectedTrace :
    ∀ z : hdata.disk hselected.index,
      z ∈ selectedExteriorExcursionDiskProtectedTraceSet hdata hselected →
        (filling z : X) = H (z : unitInterval × unitInterval)

/--
%%handwave
name:
  Protected trace extension gives closure-filling data
statement:
  A closure-valued extension of the protected trace gives the selected
  exterior disk closure-filling data.
proof:
  Forget the codomain restriction from \(\overline F\) to the ambient surface.
  The selected frontier and retained frontiers are contained in the protected
  trace, so the trace agreement gives the required equalities.
-/
noncomputable def
    SelectedExteriorExcursionDiskProtectedTraceExtensionData.toClosureFillingData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    (hext :
      SelectedExteriorExcursionDiskProtectedTraceExtensionData
        (F := F) H hdata hselected) :
    SelectedExteriorExcursionDiskClosureFillingData
      (F := F) H hdata hselected where
  filling :=
    { toFun := fun z => (hext.filling z : X)
      continuous_toFun :=
        continuous_subtype_val.comp hext.filling.continuous_toFun }
  filling_mapsTo_closure := by
    intro z _hz
    exact (hext.filling z).2
  eqOn_selected_frontier := by
    intro z hzDisk hzFrontier
    exact hext.eqOn_protectedTrace ⟨z, hzDisk⟩
      (by
        left
        exact hzFrontier)
  eqOn_retained_frontiers := by
    intro j z hzDisk hzFrontier
    exact hext.eqOn_protectedTrace ⟨z, hzDisk⟩
      (by
        right
        exact retainedExteriorExcursionDisk_frontier_subset_retainedFrontierSet
          (F := F) hdata hselected j hzFrontier)

/--
%%handwave
name:
  Region-level closure patch square data for a selected exterior disk
statement:
  Region-level closure patch square data is a continuous replacement square
  that sends the selected patch region into \(\overline F\) and agrees with
  the old square outside that patch region.
-/
structure SelectedExteriorExcursionClosurePatchRegionMapData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Type 1 where
  map : C(unitInterval × unitInterval, X)
  patchRegion_mapsTo_closure :
    MapsTo map
      (selectedExteriorExcursionPatchRegion hdata hselected) (closure F)
  eqOn_off_patchRegion :
    EqOn map H (selectedExteriorExcursionPatchRegion hdata hselected)ᶜ

/--
%%handwave
name:
  Selected disk closure filling gives region-level closure patch data
statement:
  A closure-valued filling of the selected closed parameter disk gives a
  region-level closure patch square.
proof:
  Paste the filling on the selected closed disk with the old homotopy on its
  complement.  The two maps agree on the selected frontier, so the pasting is
  continuous.  Points in the patch region lie in the selected disk, and points
  outside the patch region are either outside the selected interior, where the
  pasted map is the old one, or on a retained frontier, where the filling is
  required to agree with the old map.
-/
noncomputable def
    SelectedExteriorExcursionDiskClosureFillingData.toRegionMapData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    (hfilling :
      SelectedExteriorExcursionDiskClosureFillingData
        (F := F) H hdata hselected) :
    SelectedExteriorExcursionClosurePatchRegionMapData
      (F := F) H hdata hselected where
  map :=
    by
      classical
      let D : Set (unitInterval × unitInterval) :=
        hdata.disk hselected.index
      let fillingGlobal : unitInterval × unitInterval → X :=
        fun z =>
          if hz : z ∈ D then hfilling.filling ⟨z, hz⟩ else H z
      refine
        { toFun := D.piecewise fillingGlobal H
          continuous_toFun := ?_ }
      have hD_closed : IsClosed D := by
        simpa [D] using
          selectedExteriorExcursionDisk_isClosed (F := F) H hdata hselected
      have hfrontier_eq :
          ∀ z ∈ frontier D, fillingGlobal z = H z := by
        intro z hzFrontier
        have hzClosure : z ∈ closure D := frontier_subset_closure hzFrontier
        have hzD : z ∈ D := by
          simpa [hD_closed.closure_eq] using hzClosure
        simpa [fillingGlobal, hzD] using
          hfilling.eqOn_selected_frontier hzD (by simpa [D] using hzFrontier)
      have hfilling_continuousOn :
          ContinuousOn fillingGlobal (closure D) := by
        rw [hD_closed.closure_eq]
        rw [continuousOn_iff_continuous_restrict]
        have hrestrict :
            D.restrict fillingGlobal = fun z : D => hfilling.filling z := by
          ext z
          simp [Set.restrict, fillingGlobal, z.2]
        rw [hrestrict]
        exact hfilling.filling.continuous_toFun
      have hH_continuousOn :
          ContinuousOn H (closure Dᶜ) :=
        (ContinuousMap.HomotopyWith.continuous H).continuousOn
      exact continuous_piecewise hfrontier_eq hfilling_continuousOn hH_continuousOn
  patchRegion_mapsTo_closure := by
    intro z hz
    classical
    let D : Set (unitInterval × unitInterval) :=
      hdata.disk hselected.index
    let fillingGlobal : unitInterval × unitInterval → X :=
      fun z =>
        if hz : z ∈ D then hfilling.filling ⟨z, hz⟩ else H z
    have hzD : z ∈ D := by
      exact interior_subset hz.1
    have hEq :
        D.piecewise fillingGlobal H z = hfilling.filling ⟨z, hzD⟩ := by
      simp [D, fillingGlobal, hzD]
    have hClosure : hfilling.filling ⟨z, hzD⟩ ∈ closure F :=
      hfilling.filling_mapsTo_closure (mem_univ _)
    change D.piecewise fillingGlobal H z ∈ closure F
    rwa [hEq]
  eqOn_off_patchRegion := by
    intro z hz
    classical
    let D : Set (unitInterval × unitInterval) :=
      hdata.disk hselected.index
    let fillingGlobal : unitInterval × unitInterval → X :=
      fun z =>
        if hz : z ∈ D then hfilling.filling ⟨z, hz⟩ else H z
    have hD_closed : IsClosed D := by
      simpa [D] using
        selectedExteriorExcursionDisk_isClosed (F := F) H hdata hselected
    by_cases hzInterior : z ∈ interior D
    · have hzRetained :
          z ∈ finiteExteriorExcursionRetainedFrontierSet hdata hselected := by
        by_contra hzNotRetained
        exact hz ⟨by simpa [D] using hzInterior, hzNotRetained⟩
      have hzD : z ∈ D := interior_subset hzInterior
      have hEqFill : hfilling.filling ⟨z, hzD⟩ = H z := by
        change z ∈ ⋃ j : {j : hdata.ι // j ≠ hselected.index},
          frontier (hdata.disk (j : hdata.ι)) at hzRetained
        rcases mem_iUnion.mp hzRetained with ⟨j, hzFrontier⟩
        exact hfilling.eqOn_retained_frontiers j hzD hzFrontier
      have hPiece :
          D.piecewise fillingGlobal H z = hfilling.filling ⟨z, hzD⟩ := by
        simp [D, fillingGlobal, hzD]
      change D.piecewise fillingGlobal H z = H z
      rw [hPiece, hEqFill]
    · by_cases hzD : z ∈ D
      · have hzFrontier : z ∈ frontier D := by
          rw [frontier, mem_diff]
          exact ⟨by simpa [hD_closed.closure_eq] using hzD, hzInterior⟩
        have hEqFill : hfilling.filling ⟨z, hzD⟩ = H z :=
          hfilling.eqOn_selected_frontier hzD (by simpa [D] using hzFrontier)
        have hPiece :
            D.piecewise fillingGlobal H z = hfilling.filling ⟨z, hzD⟩ := by
          simp [D, fillingGlobal, hzD]
        change D.piecewise fillingGlobal H z = H z
        rw [hPiece, hEqFill]
      · have hPiece : D.piecewise fillingGlobal H z = H z := by
          simp [D, fillingGlobal, hzD]
        change D.piecewise fillingGlobal H z = H z
        exact hPiece

/--
%%handwave
name:
  Region-level closure patch data gives supported closure patch data
statement:
  A patch supported on the selected interior with retained frontiers removed
  gives supported closure patch square data.
proof:
  Off the selected interior the point is outside the patch region, so the map
  is unchanged.  On a retained frontier the point is also outside the patch
  region, so retained frontiers are unchanged.  For a point of the selected
  interior, either it lies in the patch region and maps into \(\overline F\),
  or it lies on a retained frontier, where the old map already lands in the
  frontier of \(F\).
-/
noncomputable def
    SelectedExteriorExcursionClosurePatchRegionMapData.toSupportedMapData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    (hregion :
      SelectedExteriorExcursionClosurePatchRegionMapData
        (F := F) H hdata hselected) :
    SelectedExteriorExcursionClosurePatchSupportedMapData
      (F := F) H hdata hselected where
  map := hregion.map
  selectedInterior_mapsTo_closure := by
    intro z hzSelected
    by_cases hzPatch :
        z ∈ selectedExteriorExcursionPatchRegion hdata hselected
    · exact hregion.patchRegion_mapsTo_closure hzPatch
    · have hzRetained :
          z ∈ finiteExteriorExcursionRetainedFrontierSet hdata hselected := by
        by_contra hzNotRetained
        exact hzPatch ⟨hzSelected, hzNotRetained⟩
      have hEq : hregion.map z = H z :=
        hregion.eqOn_off_patchRegion hzPatch
      have hHclosure : H z ∈ closure F :=
        finiteExteriorExcursionRetainedFrontierSet_mapsTo_closure
          (F := F) hdata hselected hzRetained
      simpa [hEq] using hHclosure
  eqOn_off_selectedInterior := by
    intro z hzOffSelected
    exact hregion.eqOn_off_patchRegion
      (by
        intro hzPatch
        exact hzOffSelected hzPatch.1)
  eqOn_remaining_frontiers := by
    intro j z hzFrontier
    have hzRetained :
        z ∈ finiteExteriorExcursionRetainedFrontierSet hdata hselected :=
      retainedExteriorExcursionDisk_frontier_subset_retainedFrontierSet
        (F := F) hdata hselected j hzFrontier
    exact hregion.eqOn_off_patchRegion
      (by
        intro hzPatch
        exact hzPatch.2 hzRetained)

/--
%%handwave
name:
  Supported closure patch square data gives closure patch map data
statement:
  If a closure patch square is fixed off the selected disk interior, then it
  has the original path sides and fixed endpoints.
proof:
  The selected disk interior lies away from the boundary of the homotopy
  square.  Hence the patch agrees with the old square on all four sides.
-/
noncomputable def
    SelectedExteriorExcursionClosurePatchSupportedMapData.toClosurePatchMapData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    (hsupported :
      SelectedExteriorExcursionClosurePatchSupportedMapData
        (F := F) H hdata hselected) :
    SelectedExteriorExcursionClosurePatchMapData
      (F := F) H hdata hselected where
  map := hsupported.map
  source_path := by
    intro s
    have hzBoundary : ((0 : unitInterval), s) ∈ unitSquareBoundary := by
      exact Or.inl rfl
    have hzOffSelected :
        ((0 : unitInterval), s) ∈
          (interior (hdata.disk hselected.index))ᶜ :=
      unitSquareBoundary_subset_compl_selectedExteriorExcursionDisk_interior
        (F := F) H hdata hselected hzBoundary
    simpa using hsupported.eqOn_off_selectedInterior hzOffSelected
  target_path := by
    intro s
    have hzBoundary : ((1 : unitInterval), s) ∈ unitSquareBoundary := by
      exact Or.inr (Or.inl rfl)
    have hzOffSelected :
        ((1 : unitInterval), s) ∈
          (interior (hdata.disk hselected.index))ᶜ :=
      unitSquareBoundary_subset_compl_selectedExteriorExcursionDisk_interior
        (F := F) H hdata hselected hzBoundary
    simpa using hsupported.eqOn_off_selectedInterior hzOffSelected
  left_endpoint := by
    intro t
    have hzBoundary : (t, (0 : unitInterval)) ∈ unitSquareBoundary := by
      exact Or.inr (Or.inr (Or.inl rfl))
    have hzOffSelected :
        (t, (0 : unitInterval)) ∈
          (interior (hdata.disk hselected.index))ᶜ :=
      unitSquareBoundary_subset_compl_selectedExteriorExcursionDisk_interior
        (F := F) H hdata hselected hzBoundary
    have hEq : hsupported.map (t, (0 : unitInterval)) = H (t, 0) :=
      hsupported.eqOn_off_selectedInterior hzOffSelected
    simp [hEq]
  right_endpoint := by
    intro t
    have hzBoundary : (t, (1 : unitInterval)) ∈ unitSquareBoundary := by
      exact Or.inr (Or.inr (Or.inr rfl))
    have hzOffSelected :
        (t, (1 : unitInterval)) ∈
          (interior (hdata.disk hselected.index))ᶜ :=
      unitSquareBoundary_subset_compl_selectedExteriorExcursionDisk_interior
        (F := F) H hdata hselected hzBoundary
    have hEq : hsupported.map (t, (1 : unitInterval)) = H (t, 1) :=
      hsupported.eqOn_off_selectedInterior hzOffSelected
    simp [hEq]
  selectedInterior_mapsTo_closure :=
    hsupported.selectedInterior_mapsTo_closure
  eqOn_off_selectedInterior :=
    hsupported.eqOn_off_selectedInterior
  eqOn_remaining_frontiers :=
    hsupported.eqOn_remaining_frontiers

/--
%%handwave
name:
  Closure patch map data gives closure patch homotopy data
statement:
  A continuous closure patch square with the correct path sides and fixed
  endpoints packages as closure patch homotopy data.
proof:
  Use the path-side equations to build a homotopy between the two given paths,
  and use the endpoint equations for the relative endpoint condition.
-/
noncomputable def
    SelectedExteriorExcursionClosurePatchMapData.toClosurePatchData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    (hmap :
      SelectedExteriorExcursionClosurePatchMapData
        (F := F) H hdata hselected) :
    SelectedExteriorExcursionClosurePatchData
      (F := F) H hdata hselected where
  homotopy :=
    { toHomotopy :=
        { toContinuousMap := hmap.map
          map_zero_left := hmap.source_path
          map_one_left := hmap.target_path }
      prop' := by
        intro t f hf
        rcases hf with hf | hf
        · subst f
          simpa using hmap.left_endpoint t
        · subst f
          simpa using hmap.right_endpoint t }
  selectedInterior_mapsTo_closure :=
    hmap.selectedInterior_mapsTo_closure
  eqOn_off_selectedInterior :=
    hmap.eqOn_off_selectedInterior
  eqOn_remaining_frontiers :=
    hmap.eqOn_remaining_frontiers

/--
%%handwave
name:
  Supported trace-level selected exterior-disk surgery data
statement:
  Supported trace-level selected-disk surgery data is a replacement homotopy
  whose exterior trace is the old exterior trace with the selected disk
  interior deleted, which is unchanged off the selected disk interior, and
  which is unchanged on the frontiers of the retained disks.
-/
structure SelectedExteriorExcursionSupportedTraceSurgeryData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Type 1 where
  homotopy : γ₀.Homotopy γ₁
  boundary_mapsTo : ∀ z, z ∈ unitSquareBoundary → homotopy z ∈ F
  exterior_eq_old_diff_selected :
    pathHomotopyExteriorSet (F := F) homotopy =
      pathHomotopyExteriorSet (F := F) H \
        interior (hdata.disk hselected.index)
  eqOn_off_selectedInterior :
    EqOn homotopy H (interior (hdata.disk hselected.index))ᶜ
  eqOn_remaining_frontiers :
    ∀ j : {j : hdata.ι // j ≠ hselected.index},
      EqOn homotopy H (frontier (hdata.disk (j : hdata.ι)))

/--
%%handwave
name:
  Closure patch data gives supported trace-level surgery data
statement:
  A selected-disk closure patch gives supported trace-level surgery data:
  its exterior trace is exactly the old exterior trace with the selected disk
  interior removed.
proof:
  On the selected disk interior, the patched homotopy lies in \(\overline F\),
  so it has no exterior points there.  Off that interior it agrees with the
  old homotopy, so the exterior set is exactly the old exterior set restricted
  to the complement of the selected interior.  Since the selected interior
  avoids the square boundary, the old boundary condition is preserved.
-/
noncomputable def
    SelectedExteriorExcursionClosurePatchData.toSupportedTraceSurgeryData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    (hpatch :
      SelectedExteriorExcursionClosurePatchData
        (F := F) H hdata hselected)
    (hboundary : ∀ z, z ∈ unitSquareBoundary → H z ∈ F) :
    SelectedExteriorExcursionSupportedTraceSurgeryData
      (F := F) H hdata hselected where
  homotopy := hpatch.homotopy
  boundary_mapsTo := by
    intro z hzBoundary
    have hz_off_selected :
        z ∈ (interior (hdata.disk hselected.index))ᶜ :=
      unitSquareBoundary_subset_compl_selectedExteriorExcursionDisk_interior
        (F := F) H hdata hselected hzBoundary
    have hEq : hpatch.homotopy z = H z :=
      hpatch.eqOn_off_selectedInterior hz_off_selected
    simpa [hEq] using hboundary z hzBoundary
  exterior_eq_old_diff_selected := by
    ext z
    constructor
    · intro hzExterior
      have hz_not_selected :
          z ∉ interior (hdata.disk hselected.index) := by
        intro hzSelected
        exact hzExterior
          (hpatch.selectedInterior_mapsTo_closure hzSelected)
      have hEq : hpatch.homotopy z = H z :=
        hpatch.eqOn_off_selectedInterior hz_not_selected
      have hzOldExterior :
          z ∈ pathHomotopyExteriorSet (F := F) H := by
        intro hzClosure
        exact hzExterior (by simpa [← hEq] using hzClosure)
      exact ⟨hzOldExterior, hz_not_selected⟩
    · intro hz
      rcases hz with ⟨hzOldExterior, hz_not_selected⟩
      have hEq : hpatch.homotopy z = H z :=
        hpatch.eqOn_off_selectedInterior hz_not_selected
      intro hzClosure
      exact hzOldExterior (by simpa [hEq] using hzClosure)
  eqOn_off_selectedInterior := hpatch.eqOn_off_selectedInterior
  eqOn_remaining_frontiers := hpatch.eqOn_remaining_frontiers

/--
%%handwave
name:
  Supported trace-level surgery gives trace-level surgery data
statement:
  If selected-disk surgery is supported in the selected disk interior, then it
  supplies the usual trace-level surgery data.
proof:
  The only extra point is agreement on retained disk interiors.  Each retained
  disk interior is disjoint from the selected disk interior, so the
  off-selected-interior support condition gives the required agreement there.
-/
noncomputable def
    SelectedExteriorExcursionSupportedTraceSurgeryData.toTraceSurgeryData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    (hsupported :
      SelectedExteriorExcursionSupportedTraceSurgeryData
        (F := F) H hdata hselected) :
    SelectedExteriorExcursionTraceSurgeryData
      (F := F) H hdata hselected where
  homotopy := hsupported.homotopy
  boundary_mapsTo := hsupported.boundary_mapsTo
  exterior_eq_old_diff_selected :=
    hsupported.exterior_eq_old_diff_selected
  eqOn_remaining_interiors := by
    intro j z hz
    have hz_off_selected :
        z ∈ (interior (hdata.disk hselected.index))ᶜ :=
      retainedExteriorExcursionDisk_interior_subset_compl_selectedInterior
        (F := F) hdata hselected j hz
    exact
      hsupported.eqOn_off_selectedInterior hz_off_selected
  eqOn_remaining_frontiers := hsupported.eqOn_remaining_frontiers

/--
%%handwave
name:
  Trace-level surgery data gives core selected surgery data
statement:
  If a replacement homotopy has exterior trace equal to the old exterior trace
  with the selected disk interior deleted, then it has the core retained-trace
  surgery property.
proof:
  The old exterior trace minus the selected disk interior is exactly the
  retained exterior-excursion trace.
-/
noncomputable def SelectedExteriorExcursionTraceSurgeryData.toCoreData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    (htrace :
      SelectedExteriorExcursionTraceSurgeryData
        (F := F) H hdata hselected) :
    SelectedExteriorExcursionSurgeryHomotopyCoreData
      (F := F) H hdata hselected where
  homotopy := htrace.homotopy
  boundary_mapsTo := htrace.boundary_mapsTo
  exterior_eq_remaining := by
    rw [htrace.exterior_eq_old_diff_selected]
    exact exteriorSet_diff_selectedInterior_eq_finiteExteriorExcursionRemainingSet
      (F := F) hdata hselected
  eqOn_remaining_interiors := htrace.eqOn_remaining_interiors
  eqOn_remaining_frontiers := htrace.eqOn_remaining_frontiers

/--
%%handwave
name:
  Selected exterior-disk replacement homotopy data
statement:
  A replacement homotopy for a selected exterior disk is a homotopy with the
  same path endpoints, boundary still in \(F\), whose exterior part is
  exactly the union of the old exterior disks except the selected one.
-/
structure SelectedExteriorExcursionReplacementHomotopyData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Type 1 where
  homotopy : γ₀.Homotopy γ₁
  boundary_mapsTo : ∀ z, z ∈ unitSquareBoundary → homotopy z ∈ F
  exterior_eq_remaining :
    pathHomotopyExteriorSet (F := F) homotopy =
      finiteExteriorExcursionRemainingSet hdata hselected
  interior_maps_to_exterior :
    ∀ j : {j : hdata.ι // j ≠ hselected.index},
      MapsTo homotopy (interior (hdata.disk (j : hdata.ι))) (closure F)ᶜ
  frontier_maps_to_frontier :
    ∀ j : {j : hdata.ι // j ≠ hselected.index},
      MapsTo homotopy (frontier (hdata.disk (j : hdata.ι))) (frontier F)

/--
%%handwave
name:
  Replacement homotopy data gives finite exterior-excursion data
statement:
  If a replacement homotopy has exterior part exactly the old finite family
  with the selected disk removed, then it carries finite exterior-excursion
  data indexed by the remaining disks.
proof:
  Keep the old disks with index different from the selected one.  Closedness,
  containment in the parameter-square interior, and pairwise disjointness are
  inherited from the original finite family.
-/
noncomputable def
    SelectedExteriorExcursionReplacementHomotopyData.toFiniteExteriorExcursionData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    (hrepl :
      SelectedExteriorExcursionReplacementHomotopyData
        (F := F) H hdata hselected) :
    FiniteExteriorExcursionData (F := F) hrepl.homotopy where
  ι := {j : hdata.ι // j ≠ hselected.index}
  finite := by
    classical
    letI : Fintype hdata.ι := hdata.finite
    infer_instance
  disk := fun j => hdata.disk (j : hdata.ι)
  disk_closed := by
    intro j
    exact hdata.disk_closed (j : hdata.ι)
  disk_regular := by
    intro j
    exact hdata.disk_regular (j : hdata.ι)
  disk_subset_interior := by
    intro j
    exact hdata.disk_subset_interior (j : hdata.ι)
  exterior_eq := by
    simpa [finiteExteriorExcursionRemainingSet] using hrepl.exterior_eq_remaining
  pairwise_disjoint_interiors := by
    intro i j hij
    exact hdata.pairwise_disjoint_interiors
      (by
        intro hval
        exact hij (Subtype.ext hval))
  interior_maps_to_exterior := hrepl.interior_maps_to_exterior
  frontier_maps_to_frontier := hrepl.frontier_maps_to_frontier

/--
%%handwave
name:
  Core selected surgery homotopy data gives replacement homotopy data
statement:
  Core selected-disk surgery data gives replacement homotopy data.
proof:
  The core data already gives the replacement homotopy, the boundary
  condition, and the exact exterior trace.  On retained disk interiors and
  frontiers, the new homotopy agrees with the old one, so the old
  exterior/frontier mapping properties transfer.
-/
noncomputable def
    SelectedExteriorExcursionSurgeryHomotopyCoreData.toReplacementHomotopyData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    (hcore :
      SelectedExteriorExcursionSurgeryHomotopyCoreData
        (F := F) H hdata hselected) :
    SelectedExteriorExcursionReplacementHomotopyData
      (F := F) H hdata hselected where
  homotopy := hcore.homotopy
  boundary_mapsTo := hcore.boundary_mapsTo
  exterior_eq_remaining := hcore.exterior_eq_remaining
  interior_maps_to_exterior := by
    intro j z hz
    have hEq : hcore.homotopy z = H z :=
      hcore.eqOn_remaining_interiors j hz
    have hHz : H z ∈ (closure F)ᶜ :=
      hdata.interior_maps_to_exterior (j : hdata.ι) hz
    simpa [hEq] using hHz
  frontier_maps_to_frontier := by
    intro j z hz
    have hEq : hcore.homotopy z = H z :=
      hcore.eqOn_remaining_frontiers j hz
    have hHz : H z ∈ frontier F :=
      hdata.frontier_maps_to_frontier (j : hdata.ι) hz
    simpa [hEq] using hHz

/--
%%handwave
name:
  Selected exterior-excursion deletion step data
statement:
  A selected exterior-excursion deletion step records a replacement homotopy
  and finite exterior-excursion data whose new index set is exactly the old
  finite index set with the selected disk removed.
-/
structure SelectedExteriorExcursionDeletionStep
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Type 1 where
  homotopy : γ₀.Homotopy γ₁
  boundary_mapsTo : ∀ z, z ∈ unitSquareBoundary → homotopy z ∈ F
  data : FiniteExteriorExcursionData (F := F) homotopy
  remainingEquiv : data.ι ≃ {j : hdata.ι // j ≠ hselected.index}

/--
%%handwave
name:
  Replacement homotopy data gives a selected deletion step
statement:
  A replacement homotopy whose exterior disks are exactly the old remaining
  disks gives a selected deletion step.
proof:
  Use the remaining old disks as the new finite exterior-excursion family.
  Its index set is definitionally the old finite index set with the selected
  index removed.
-/
noncomputable def SelectedExteriorExcursionReplacementHomotopyData.toDeletionStep
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    (hrepl :
      SelectedExteriorExcursionReplacementHomotopyData
        (F := F) H hdata hselected) :
    SelectedExteriorExcursionDeletionStep (F := F) H hdata hselected where
  homotopy := hrepl.homotopy
  boundary_mapsTo := hrepl.boundary_mapsTo
  data := hrepl.toFiniteExteriorExcursionData
  remainingEquiv := Equiv.refl _

/--
%%handwave
name:
  Deleting a selected finite exterior disk gives a surgery step
statement:
  A selected exterior-excursion deletion step is a one-step finite surgery
  result: since the new index set is the old one with the selected index
  removed, the number of exterior disks strictly decreases.
proof:
  The new index set is equivalent to the complement of one point in the old
  finite index set.  A finite set with one point removed has cardinality one
  less, hence strictly smaller.
-/
noncomputable def SelectedExteriorExcursionDeletionStep.toSurgeryStep
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    (hdelete :
      SelectedExteriorExcursionDeletionStep
        (F := F) H hdata hselected) :
    FiniteExteriorExcursionSurgeryStep (F := F) H hdata where
  homotopy := hdelete.homotopy
  boundary_mapsTo := hdelete.boundary_mapsTo
  data := hdelete.data
  card_lt := by
    classical
    letI : Fintype hdata.ι := hdata.finite
    letI : Fintype hdelete.data.ι := hdelete.data.finite
    haveI : Nonempty hdata.ι := ⟨hselected.index⟩
    letI : Fintype {j : hdata.ι // j ≠ hselected.index} :=
      Fintype.subtype
        ((Finset.univ : Finset hdata.ι).filter fun j => j ≠ hselected.index)
        (by
          intro j
          simp)
    letI : Fintype {j : hdata.ι // j = hselected.index} :=
      Fintype.subtype
        ((Finset.univ : Finset hdata.ι).filter fun j => j = hselected.index)
        (by
          intro j
          simp)
    have hnew_card :
        finiteExteriorExcursionDataCard hdelete.data =
          Fintype.card {j : hdata.ι // j ≠ hselected.index} := by
      simpa [finiteExteriorExcursionDataCard] using
        Fintype.card_congr hdelete.remainingEquiv
    have hcompl :
        Fintype.card {j : hdata.ι // j ≠ hselected.index} =
          Fintype.card hdata.ι - 1 := by
      have hsingle :
          Fintype.card {j : hdata.ι // j = hselected.index} = 1 :=
        Fintype.card_subtype_eq hselected.index
      calc
        Fintype.card {j : hdata.ι // j ≠ hselected.index}
            = Fintype.card hdata.ι -
                Fintype.card {j : hdata.ι // j = hselected.index} := by
              exact
                Fintype.card_subtype_compl
                  (fun j : hdata.ι => j = hselected.index)
        _ = Fintype.card hdata.ι - 1 := by
              rw [hsingle]
    have hold_pos : Fintype.card hdata.ι ≠ 0 :=
      Fintype.card_ne_zero
    rw [hnew_card, hcompl]
    exact Nat.sub_one_lt hold_pos

/--
%%handwave
name:
  Exterior-side filling of the selected disk
statement:
  The old homotopy restricted to the selected closed parameter disk is a
  continuous ambient filling of the selected exterior excursion.
proof:
  Restrict the old homotopy square to the selected closed disk.
-/
def selectedExteriorExcursionDiskExteriorFillingMap
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    C(hdata.disk hselected.index, X) where
  toFun := fun z => H (z : unitInterval × unitInterval)
  continuous_toFun :=
    (ContinuousMap.HomotopyWith.continuous H).comp continuous_subtype_val

/--
%%handwave
name:
  Values of the exterior-side filling
statement:
  The exterior-side filling of the selected disk is just the old homotopy on
  that disk.
proof:
  This is immediate from the definition.
-/
@[simp] theorem selectedExteriorExcursionDiskExteriorFillingMap_coe
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (z : hdata.disk hselected.index) :
    selectedExteriorExcursionDiskExteriorFillingMap
      (F := F) H hdata hselected z =
      H (z : unitInterval × unitInterval) := by
  rfl

/--
%%handwave
name:
  The exterior-side filling is exterior on the selected interior
statement:
  On the interior of the selected parameter disk, the exterior-side filling
  takes values outside \(\overline F\).
proof:
  This is part of the selected exterior-excursion data.
-/
theorem selectedExteriorExcursionDiskExteriorFillingMap_interior_mapsTo_exterior
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    MapsTo
      (selectedExteriorExcursionDiskExteriorFillingMap
        (F := F) H hdata hselected)
      {z : hdata.disk hselected.index |
        (z : unitInterval × unitInterval) ∈
          interior (hdata.disk hselected.index)}
      (closure F)ᶜ := by
  intro z hz
  simpa [selectedExteriorExcursionDiskExteriorFillingMap_coe] using
    hselected.interior_maps_to_exterior hz

/--
%%handwave
name:
  The exterior-side filling has the protected frontier trace
statement:
  On the protected trace, the exterior-side filling agrees with the
  frontier-valued protected trace after forgetting the target restriction.
proof:
  Both maps are the old homotopy restricted to the protected trace.
-/
theorem selectedExteriorExcursionDiskExteriorFillingMap_eq_frontierMap_on_protectedTrace
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    ∀ z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
      selectedExteriorExcursionDiskExteriorFillingMap
          (F := F) H hdata hselected
          (z : hdata.disk hselected.index) =
        (selectedExteriorExcursionDiskProtectedTraceFrontierMap
          (F := F) H hdata hselected z : X) := by
  intro z
  rfl

/--
%%handwave
name:
  The selected disk interior as a subtype
statement:
  The selected disk interior, viewed inside the selected closed parameter
  disk, is the part of the selected disk lying in its ambient interior.
-/
def selectedExteriorExcursionDiskInteriorSubtype
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Set (hdata.disk hselected.index) :=
  {z | (z : unitInterval × unitInterval) ∈
    interior (hdata.disk hselected.index)}

/--
%%handwave
name:
  The selected disk interior is dense in the selected disk
statement:
  The ambient interior of a selected regular parameter disk is dense in that
  disk, considered as a subtype.
proof:
  This is the regularity property of finite exterior-excursion disks.
-/
theorem selectedExteriorExcursionDiskInteriorSubtype_dense
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Dense (selectedExteriorExcursionDiskInteriorSubtype hdata hselected) := by
  simpa [selectedExteriorExcursionDiskInteriorSubtype] using
    hselected.disk_regular.dense_interiorSubtype

/--
%%handwave
name:
  The protected trace is approached from the selected interior
statement:
  Every protected trace point of a selected exterior disk lies in the closure
  of the selected disk interior, viewed inside the selected closed disk.
proof:
  The selected disk is regular, so its interior is dense in the closed disk.
-/
theorem selectedExteriorExcursionDiskProtectedTrace_subset_closure_interiorSubtype
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    selectedExteriorExcursionDiskProtectedTraceSet hdata hselected ⊆
      closure (selectedExteriorExcursionDiskInteriorSubtype hdata hselected) := by
  intro z _hz
  have hdense :=
    selectedExteriorExcursionDiskInteriorSubtype_dense
      (F := F) hdata hselected
  simp [hdense.closure_eq]

/--
%%handwave
name:
  Collar-surgery hypotheses for a protected trace
statement:
  The collar-surgery hypotheses record that the selected parameter disk is
  regular, the protected trace is closed and compact, the trace is approached
  from the selected disk interior, the exterior-side filling maps that
  interior outside \(\overline F\), the filling has the prescribed frontier
  trace, and the trace is covered by finitely many smooth boundary collars.
-/
structure SelectedExteriorExcursionDiskProtectedTraceCollarSurgeryHypotheses
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F))
    (Ψ : C(hdata.disk hselected.index, X))
    (t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)) : Prop where
  selected_regular : IsRegularClosedParamDisk (hdata.disk hselected.index)
  protected_closed :
    IsClosed (selectedExteriorExcursionDiskProtectedTraceSet hdata hselected)
  protected_compact :
    IsCompact (selectedExteriorExcursionDiskProtectedTraceSet hdata hselected)
  protectedTrace_adheres_to_selectedInterior :
    selectedExteriorExcursionDiskProtectedTraceSet hdata hselected ⊆
      closure (selectedExteriorExcursionDiskInteriorSubtype hdata hselected)
  exteriorSide_interior_mapsTo_exterior :
    MapsTo Ψ
      (selectedExteriorExcursionDiskInteriorSubtype hdata hselected)
      (closure F)ᶜ
  exteriorSide_eq_trace :
    ∀ z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
      Ψ (z : hdata.disk hselected.index) = (φ z : X)
  trace_mapsTo_chartCover :
    MapsTo
      (fun z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected =>
        (φ z : X))
      univ
      (⋃ x ∈ t,
        (smoothBoundary_localBoundaryChartData
          (F := F) hF_smooth (x : X)
          (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
            (F := F) hdata hselected x.2)).neighborhood)

/--
%%handwave
name:
  The selected exterior disk supplies the collar-surgery hypotheses
statement:
  The regularity of finite exterior-excursion disks, compactness of the
  protected trace, the exterior-side filling, and the finite boundary-chart
  cover supply the collar-surgery hypotheses.
proof:
  The selected disk regularity is part of the finite exterior-excursion data.
  Density of its interior gives approach from the exterior side, and the
  remaining assumptions are exactly the trace agreement and chart-cover
  hypotheses.
-/
theorem selectedExteriorExcursionDiskProtectedTraceCollarSurgeryHypotheses_of_mapsTo_chartCover
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (hprotected_closed :
      IsClosed (selectedExteriorExcursionDiskProtectedTraceSet hdata hselected))
    (hprotected_compact :
      IsCompact (selectedExteriorExcursionDiskProtectedTraceSet hdata hselected))
    (φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F))
    (Ψ : C(hdata.disk hselected.index, X))
    (hΨ_interior_mapsTo_exterior :
      MapsTo Ψ
        (selectedExteriorExcursionDiskInteriorSubtype hdata hselected)
        (closure F)ᶜ)
    (hΨ_eq_trace :
      ∀ z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        Ψ (z : hdata.disk hselected.index) = (φ z : X))
    (t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected))
    (hφ_mapsTo_chartCover :
      MapsTo
        (fun z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected =>
          (φ z : X))
        univ
        (⋃ x ∈ t,
          (smoothBoundary_localBoundaryChartData
            (F := F) hF_smooth (x : X)
            (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
              (F := F) hdata hselected x.2)).neighborhood)) :
    SelectedExteriorExcursionDiskProtectedTraceCollarSurgeryHypotheses
      (F := F) hF_smooth H hdata hselected φ Ψ t where
  selected_regular := hselected.disk_regular
  protected_closed := hprotected_closed
  protected_compact := hprotected_compact
  protectedTrace_adheres_to_selectedInterior :=
    selectedExteriorExcursionDiskProtectedTrace_subset_closure_interiorSubtype
      (F := F) hdata hselected
  exteriorSide_interior_mapsTo_exterior := hΨ_interior_mapsTo_exterior
  exteriorSide_eq_trace := hΨ_eq_trace
  trace_mapsTo_chartCover := hφ_mapsTo_chartCover

/--
%%handwave
name:
  Finite boundary-complex data for the protected trace
statement:
  The protected trace of a selected exterior disk is the selected disk
  frontier together with the frontiers of finitely many retained regular
  exterior disks with pairwise disjoint interiors.
-/
structure SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    Type 1 where
  retained_index_finite : Fintype {j : hdata.ι // j ≠ hselected.index}
  selected_regular : IsRegularClosedParamDisk (hdata.disk hselected.index)
  retained_regular :
    ∀ j : {j : hdata.ι // j ≠ hselected.index},
      IsRegularClosedParamDisk (hdata.disk (j : hdata.ι))
  selected_retained_interiors_disjoint :
    ∀ j : {j : hdata.ι // j ≠ hselected.index},
      Disjoint
        (interior (hdata.disk hselected.index))
        (interior (hdata.disk (j : hdata.ι)))
  retained_pairwise_disjoint_interiors :
    Pairwise fun j k : {j : hdata.ι // j ≠ hselected.index} =>
      Disjoint
        (interior (hdata.disk (j : hdata.ι)))
        (interior (hdata.disk (k : hdata.ι)))
  protectedTrace_eq :
    selectedExteriorExcursionDiskProtectedTraceSet hdata hselected =
      {z : hdata.disk hselected.index |
        (z : unitInterval × unitInterval) ∈
          frontier (hdata.disk hselected.index) ∨
        (z : unitInterval × unitInterval) ∈
          finiteExteriorExcursionRetainedFrontierSet hdata hselected}
  selected_frontier_subset :
    {z : hdata.disk hselected.index |
      (z : unitInterval × unitInterval) ∈
        frontier (hdata.disk hselected.index)} ⊆
      selectedExteriorExcursionDiskProtectedTraceSet hdata hselected
  retained_frontier_subset :
    ∀ j : {j : hdata.ι // j ≠ hselected.index},
      {z : hdata.disk hselected.index |
        (z : unitInterval × unitInterval) ∈
          frontier (hdata.disk (j : hdata.ι))} ⊆
        selectedExteriorExcursionDiskProtectedTraceSet hdata hselected

/--
%%handwave
name:
  The protected trace is a finite boundary complex
statement:
  The protected trace of a selected exterior disk carries finite
  boundary-complex data.
proof:
  This is the definition of the protected trace, together with the regularity
  and pairwise-disjointness data already recorded by the finite exterior
  excursions.
-/
noncomputable def selectedExteriorExcursionDiskProtectedTrace_finiteBoundaryComplexData
    {X : Type} [TopologicalSpace X] {F : Set X}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata) :
    SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
      (F := F) hdata hselected := by
  classical
  letI : Fintype hdata.ι := hdata.finite
  refine
    { retained_index_finite := ?_
      selected_regular := ?_
      retained_regular := ?_
      selected_retained_interiors_disjoint := ?_
      retained_pairwise_disjoint_interiors := ?_
      protectedTrace_eq := ?_
      selected_frontier_subset := ?_
      retained_frontier_subset := ?_ }
  · infer_instance
  · exact hselected.disk_regular
  · intro j
    exact hdata.disk_regular (j : hdata.ι)
  · intro j
    exact hdata.pairwise_disjoint_interiors
      (by
        intro h
        exact j.2 h.symm)
  · intro j k hjk
    exact hdata.pairwise_disjoint_interiors
      (by
        intro h
        exact hjk (Subtype.ext h))
  · rfl
  · intro z hz
    exact Or.inl hz
  · intro j z hz
    exact Or.inr
      ((retainedExteriorExcursionDisk_frontier_subset_retainedFrontierSet
        (F := F) hdata hselected j) hz)

/--
%%handwave
name:
  Exterior-side collar data for the protected trace
statement:
  Exterior-side collar data records exactly the local information needed near
  the protected trace: the selected disk is regular, the trace is compact,
  the exterior filling approaches the trace from outside \(\overline F\),
  the trace values agree, and finitely many smooth boundary collars cover the
  trace image.
-/
structure SelectedExteriorExcursionDiskProtectedTraceCollarSideData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F))
    (Ψ : C(hdata.disk hselected.index, X))
    (t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)) : Type 1 where
  selected_regular : IsRegularClosedParamDisk (hdata.disk hselected.index)
  protected_compact :
    IsCompact (selectedExteriorExcursionDiskProtectedTraceSet hdata hselected)
  protectedTrace_adheres_to_selectedInterior :
    selectedExteriorExcursionDiskProtectedTraceSet hdata hselected ⊆
      closure (selectedExteriorExcursionDiskInteriorSubtype hdata hselected)
  exteriorSide_interior_mapsTo_exterior :
    MapsTo Ψ
      (selectedExteriorExcursionDiskInteriorSubtype hdata hselected)
      (closure F)ᶜ
  exteriorSide_eq_trace :
    ∀ z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
      Ψ (z : hdata.disk hselected.index) = (φ z : X)
  trace_mapsTo_chartCover :
    MapsTo
      (fun z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected =>
        (φ z : X))
      univ
      (⋃ x ∈ t,
        (smoothBoundary_localBoundaryChartData
          (F := F) hF_smooth (x : X)
          (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
            (F := F) hdata hselected x.2)).neighborhood)

/--
%%handwave
name:
  Collar-surgery hypotheses give exterior-side collar data
statement:
  The collar-surgery hypotheses immediately supply the local exterior-side
  collar data.
-/
def SelectedExteriorExcursionDiskProtectedTraceCollarSideData.of_collarSurgeryHypotheses
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    (hcollar :
      SelectedExteriorExcursionDiskProtectedTraceCollarSurgeryHypotheses
        (F := F) hF_smooth H hdata hselected φ Ψ t) :
    SelectedExteriorExcursionDiskProtectedTraceCollarSideData
      (F := F) hF_smooth H hdata hselected φ Ψ t where
  selected_regular := hcollar.selected_regular
  protected_compact := hcollar.protected_compact
  protectedTrace_adheres_to_selectedInterior :=
    hcollar.protectedTrace_adheres_to_selectedInterior
  exteriorSide_interior_mapsTo_exterior :=
    hcollar.exteriorSide_interior_mapsTo_exterior
  exteriorSide_eq_trace := hcollar.exteriorSide_eq_trace
  trace_mapsTo_chartCover := hcollar.trace_mapsTo_chartCover

/--
%%handwave
name:
  The smooth boundary-chart cover of the protected trace is nonempty
statement:
  Any finite smooth boundary-chart cover supplied by exterior-side collar
  data for the protected trace is nonempty.
proof:
  The protected trace itself is nonempty.  A map from this trace cannot have
  image contained in an empty union of chart neighborhoods.
-/
theorem SelectedExteriorExcursionDiskProtectedTraceCollarSideData.chartCover_ne_empty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    (hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t) :
    t ≠ ∅ := by
  intro ht
  rcases selectedExteriorExcursionDiskProtectedTraceSet_nonempty
    (F := F) hdata hselected with ⟨z, hz⟩
  let zTrace :
      selectedExteriorExcursionDiskProtectedTraceSet hdata hselected :=
    ⟨z, hz⟩
  have hzcover :
      (φ zTrace : X) ∈
        (⋃ x ∈ t,
          (smoothBoundary_localBoundaryChartData
            (F := F) hF_smooth (x : X)
            (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
              (F := F) hdata hselected x.2)).neighborhood) :=
    hside.trace_mapsTo_chartCover (by simp)
  rw [ht] at hzcover
  simp at hzcover

/--
%%handwave
name:
  Collar-strip decomposition data for the protected trace
statement:
  A collar-strip decomposition consists of a neighborhood of the finite
  protected trace controlled by finitely many smooth boundary collars, whose
  complement in the selected disk is packaged as at most one compact
  remainder region.
-/
structure SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F))
    (Ψ : C(hdata.disk hselected.index, X))
    (t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected))
    (_hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected)
    (_hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t) :
    Type 1 where
  strip : Set (hdata.disk hselected.index)
  strip_open : IsOpen strip
  protectedTrace_subset_strip :
    selectedExteriorExcursionDiskProtectedTraceSet hdata hselected ⊆ strip
  piece : Type
  piece_finite : Fintype piece
  piece_subsingleton : Subsingleton piece
  region : piece → Set (hdata.disk hselected.index)
  region_compact : ∀ P : piece, IsCompact (region P)
  regionClosedDiskHomeomorph :
    ∀ P : piece, region P ≃ₜ Metric.closedBall (0 : ℂ) 1
  region_attachment_eq_boundary :
    ∀ P : piece,
      {z : region P | (z : hdata.disk hselected.index) ∈ closure strip} =
        {z : region P |
          (((regionClosedDiskHomeomorph P) z :
              Metric.closedBall (0 : ℂ) 1) : ℂ) ∈
            Metric.sphere (0 : ℂ) 1}
  stripClosure_mapsTo_exteriorSideChartCover :
    MapsTo
      (fun z : closure strip => Ψ (z : hdata.disk hselected.index))
      univ
      (⋃ x ∈ t,
        (smoothBoundary_localBoundaryChartData
          (F := F) hF_smooth (x : X)
          (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
            (F := F) hdata hselected x.2)).neighborhood)
  strip_complement_subset_regions : stripᶜ ⊆ ⋃ P : piece, region P
  regions_subset_strip_complement : (⋃ P : piece, region P) ⊆ stripᶜ

/--
%%handwave
name:
  Controlled parameter collar-strip decomposition data
statement:
  Parameter collar-strip decomposition data records a collar of the finite
  protected boundary complex inside the selected closed disk, together with
  smooth-boundary chart control on the closed collar and the compact
  closed-disk remainder regions left outside that collar.
-/
structure SelectedExteriorExcursionDiskProtectedTraceParameterCollarStripDecompositionData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (Ψ : C(hdata.disk hselected.index, X))
    (t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected))
    (_hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected) :
    Type 1 where
  strip : Set (hdata.disk hselected.index)
  strip_open : IsOpen strip
  protectedTrace_subset_strip :
    selectedExteriorExcursionDiskProtectedTraceSet hdata hselected ⊆ strip
  piece : Type
  piece_finite : Fintype piece
  piece_subsingleton : Subsingleton piece
  region : piece → Set (hdata.disk hselected.index)
  region_compact : ∀ P : piece, IsCompact (region P)
  regionClosedDiskHomeomorph :
    ∀ P : piece, region P ≃ₜ Metric.closedBall (0 : ℂ) 1
  region_attachment_eq_boundary :
    ∀ P : piece,
      {z : region P | (z : hdata.disk hselected.index) ∈ closure strip} =
        {z : region P |
          (((regionClosedDiskHomeomorph P) z :
              Metric.closedBall (0 : ℂ) 1) : ℂ) ∈
            Metric.sphere (0 : ℂ) 1}
  stripClosure_mapsTo_exteriorSideChartCover :
    MapsTo
      (fun z : closure strip => Ψ (z : hdata.disk hselected.index))
      univ
      (⋃ x ∈ t,
        (smoothBoundary_localBoundaryChartData
          (F := F) hF_smooth (x : X)
          (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
            (F := F) hdata hselected x.2)).neighborhood)
  strip_complement_subset_regions : stripᶜ ⊆ ⋃ P : piece, region P
  regions_subset_strip_complement : (⋃ P : piece, region P) ⊆ stripᶜ





/--
%%handwave
name:
  Points outside the collar strip lie in the selected disk interior
statement:
  If the collar strip contains the protected trace, then every point of the
  selected closed disk outside the strip lies in the selected disk interior.
proof:
  A point of the selected closed disk which is not in its interior lies on
  the selected frontier, since the selected disk is closed.  The selected
  frontier is part of the protected trace, and the protected trace lies in
  the strip.  Hence a point outside the strip cannot be such a frontier
  point.
-/
theorem selectedExteriorExcursionDiskProtectedTraceCollarStripDecomposition_strip_compl_subset_selectedInterior
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside) :
    hdecomp.stripᶜ ⊆
      selectedExteriorExcursionDiskInteriorSubtype hdata hselected := by
  intro z hzStrip
  change
    (z : unitInterval × unitInterval) ∈
      interior (hdata.disk hselected.index)
  by_contra hzInterior
  have hzFrontier :
      (z : unitInterval × unitInterval) ∈
        frontier (hdata.disk hselected.index) := by
    rw [frontier, mem_diff]
    have hzClosure :
        (z : unitInterval × unitInterval) ∈
          closure (hdata.disk hselected.index) := by
      simp [(selectedExteriorExcursionDisk_isClosed
        (F := F) H hdata hselected).closure_eq, z.2]
    exact ⟨hzClosure, hzInterior⟩
  have hzProtected :
      z ∈ selectedExteriorExcursionDiskProtectedTraceSet hdata hselected := by
    left
    exact hzFrontier
  exact hzStrip (hdecomp.protectedTrace_subset_strip hzProtected)

/--
%%handwave
name:
  Collar-strip pieces lie in the selected disk interior
statement:
  Every complementary piece of a collar-strip decomposition lies in the
  selected disk interior.
proof:
  The pieces are contained in the complement of the strip, and the complement
  of the strip is contained in the selected disk interior.
-/
theorem selectedExteriorExcursionDiskProtectedTraceCollarStripDecomposition_region_subset_selectedInterior
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside)
    (P : hdecomp.piece) :
    hdecomp.region P ⊆
      selectedExteriorExcursionDiskInteriorSubtype hdata hselected := by
  intro z hzRegion
  exact
    selectedExteriorExcursionDiskProtectedTraceCollarStripDecomposition_strip_compl_subset_selectedInterior
      (F := F) hdecomp
      (hdecomp.regions_subset_strip_complement
        (mem_iUnion_of_mem P hzRegion))

/--
%%handwave
name:
  Exterior-side filling restricted to a collar-strip piece
statement:
  The exterior-side filling restricts to a continuous map on each
  complementary piece of the collar-strip decomposition.
-/
def selectedExteriorExcursionDiskProtectedTrace_pieceExteriorSideMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside)
    (P : hdecomp.piece) :
    C(hdecomp.region P, X) where
  toFun := fun z => Ψ (z : hdata.disk hselected.index)
  continuous_toFun :=
    Ψ.continuous_toFun.comp continuous_subtype_val

/--
%%handwave
name:
  Piece exterior-side maps are exterior-valued
statement:
  On every complementary piece of the collar-strip decomposition, the
  restricted exterior-side filling takes values in
  \(X\setminus\overline F\).
proof:
  Each piece lies in the selected disk interior, and the exterior-side collar
  data says that \(\Psi\) maps the selected disk interior outside
  \(\overline F\).
-/
theorem selectedExteriorExcursionDiskProtectedTrace_pieceExteriorSideMap_mapsTo_exterior
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside)
    (P : hdecomp.piece) :
    MapsTo
      (selectedExteriorExcursionDiskProtectedTrace_pieceExteriorSideMap
        (F := F) hdecomp P)
      univ
      (closure F)ᶜ := by
  intro z _hz
  exact hside.exteriorSide_interior_mapsTo_exterior
    (selectedExteriorExcursionDiskProtectedTraceCollarStripDecomposition_region_subset_selectedInterior
      (F := F) hdecomp P z.2)

/--
%%handwave
name:
  Exterior-side tracking data for collar-strip pieces
statement:
  Exterior-side tracking data records that the old exterior-side filling
  restricts to every complementary piece and that these restrictions are
  exterior-valued.
-/
structure SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside) :
    Type 1 where
  exteriorPieceMap : ∀ P : hdecomp.piece, C(hdecomp.region P, X)
  exteriorPieceMap_eq_psi :
    ∀ (P : hdecomp.piece) (z : hdecomp.region P),
      exteriorPieceMap P z = Ψ (z : hdata.disk hselected.index)
  exteriorPieceMap_mapsTo_exterior :
    ∀ P : hdecomp.piece,
      MapsTo (exteriorPieceMap P) univ (closure F)ᶜ

/--
%%handwave
name:
  The exterior-side filling tracks all collar-strip pieces
statement:
  The exterior-side filling supplies exterior-valued tracking data on every
  complementary piece of a collar-strip decomposition.
proof:
  Restrict \(\Psi\) to each piece.  The previous lemma places each piece in
  the selected disk interior, where \(\Psi\) is exterior-valued.
-/
def selectedExteriorExcursionDiskProtectedTrace_exteriorSidePieceTrackingData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside) :
    SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
      (F := F) hdecomp where
  exteriorPieceMap := fun P =>
    selectedExteriorExcursionDiskProtectedTrace_pieceExteriorSideMap
      (F := F) hdecomp P
  exteriorPieceMap_eq_psi := by
    intro P z
    rfl
  exteriorPieceMap_mapsTo_exterior := by
    intro P
    exact
      selectedExteriorExcursionDiskProtectedTrace_pieceExteriorSideMap_mapsTo_exterior
        (F := F) hdecomp P

/--
%%handwave
name:
  The collar-strip regions are exactly the strip complement
statement:
  In a collar-strip decomposition, the union of the finitely many remainder
  regions is exactly the complement of the strip.
proof:
  This is the pair of containment properties recorded in the decomposition
  data.
-/
theorem selectedExteriorExcursionDiskProtectedTraceCollarStripDecomposition_regions_eq_strip_compl
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside) :
    (⋃ P : hdecomp.piece, hdecomp.region P) = hdecomp.stripᶜ :=
  subset_antisymm
    hdecomp.regions_subset_strip_complement
    hdecomp.strip_complement_subset_regions

/--
%%handwave
name:
  The collar strip and regions cover the selected disk
statement:
  In a collar-strip decomposition, the strip together with the finitely many
  remainder regions covers the selected closed disk.
proof:
  A point is either in the strip or in its complement, and the complement is
  exactly the union of the remainder regions.
-/
theorem selectedExteriorExcursionDiskProtectedTraceCollarStripDecomposition_strip_union_regions_eq_univ
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside) :
    hdecomp.strip ∪ (⋃ P : hdecomp.piece, hdecomp.region P) = univ := by
  rw [
    selectedExteriorExcursionDiskProtectedTraceCollarStripDecomposition_regions_eq_strip_compl
      (F := F) hdecomp]
  exact union_compl_self hdecomp.strip

/--
%%handwave
name:
  Finite cover data for collar-strip pasting
statement:
  The strip and finitely many compact remainder regions form the finite cover
  used by the later pasting step.
-/
structure SelectedExteriorExcursionDiskProtectedTracePastingCoverData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside) :
    Type 1 where
  piece_finite : Fintype hdecomp.piece
  region_compact : ∀ P : hdecomp.piece, IsCompact (hdecomp.region P)
  regions_eq_strip_compl :
    (⋃ P : hdecomp.piece, hdecomp.region P) = hdecomp.stripᶜ
  cover_eq_univ :
    hdecomp.strip ∪ (⋃ P : hdecomp.piece, hdecomp.region P) = univ

/--
%%handwave
name:
  A collar-strip decomposition supplies finite pasting cover data
statement:
  Every collar-strip decomposition supplies the finite cover data for the
  later pasting step.
proof:
  Use the finite index set and compactness of the recorded regions, together
  with the equality between the union of the regions and the strip
  complement.
-/
def selectedExteriorExcursionDiskProtectedTrace_pastingCoverData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside) :
    SelectedExteriorExcursionDiskProtectedTracePastingCoverData
      (F := F) hdecomp where
  piece_finite := hdecomp.piece_finite
  region_compact := hdecomp.region_compact
  regions_eq_strip_compl :=
    selectedExteriorExcursionDiskProtectedTraceCollarStripDecomposition_regions_eq_strip_compl
      (F := F) hdecomp
  cover_eq_univ :=
    selectedExteriorExcursionDiskProtectedTraceCollarStripDecomposition_strip_union_regions_eq_univ
      (F := F) hdecomp

/--
%%handwave
name:
  Closed-side piece fillings after collar-strip removal
statement:
  Given a collar-strip decomposition, the no-compact-complement hypothesis
  turns the exterior-side fillings of the remaining boundary curves into
  fillings on the \(\overline F\)-side, compatible with the collar-strip
  filling and therefore giving a pasted filling of the selected disk.
-/
structure SelectedExteriorExcursionDiskProtectedTraceClosedSidePieceFillingData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside) :
    Type 1 where
  stripFilling : C(hdecomp.strip, closure F)
  strip_eqOn_trace :
    ∀ z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
      stripFilling ⟨(z : hdata.disk hselected.index),
          hdecomp.protectedTrace_subset_strip z.2⟩ =
        (⟨(φ z : X), frontier_subset_closure (φ z).2⟩ : closure F)
  pieceFilling : ∀ P : hdecomp.piece, C(hdecomp.region P, closure F)
  pastedFilling : C(hdata.disk hselected.index, closure F)
  pastedFilling_eqOn_strip :
    ∀ z : hdecomp.strip,
      pastedFilling (z : hdata.disk hselected.index) = stripFilling z
  pastedFilling_eqOn_region :
    ∀ (P : hdecomp.piece) (z : hdecomp.region P),
      pastedFilling (z : hdata.disk hselected.index) = pieceFilling P z
  pastedFilling_eqOn_trace :
    ∀ z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
      pastedFilling (z : hdata.disk hselected.index) =
        (⟨(φ z : X), frontier_subset_closure (φ z).2⟩ : closure F)

/--
%%handwave
name:
  Compatible closed-side piece fillings give a closed-side extension
statement:
  Compatible closed-side fillings of the collar strip and the finitely many
  complementary regions immediately give the corresponding
  \(\overline F\)-valued filling of the selected parameter disk.
-/
theorem SelectedExteriorExcursionDiskProtectedTraceClosedSidePieceFillingData.exists_extension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    (hpieces :
      SelectedExteriorExcursionDiskProtectedTraceClosedSidePieceFillingData
        (F := F) hdecomp) :
    ∃ Φ : C(hdata.disk hselected.index, closure F),
      ∀ z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        Φ (z : hdata.disk hselected.index) =
          (⟨(φ z : X), frontier_subset_closure (φ z).2⟩ : closure F) :=
  ⟨hpieces.pastedFilling, hpieces.pastedFilling_eqOn_trace⟩

/--
%%handwave
name:
  Closed-side collar-strip filling data
statement:
  Closed-side collar-strip filling data is a continuous map from the collar
  strip into \(\overline F\), together with a continuous extension to the
  closed strip.  On the protected trace it agrees with the prescribed
  frontier trace.
-/
structure SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside) :
    Type 1 where
  stripFilling : C(hdecomp.strip, closure F)
  stripClosureFilling : C(closure hdecomp.strip, closure F)
  stripClosureFilling_eqOn_strip :
    ∀ z : hdecomp.strip,
      stripClosureFilling
          ⟨(z : hdata.disk hselected.index), subset_closure z.2⟩ =
        stripFilling z
  strip_eqOn_trace :
    ∀ z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
      stripFilling ⟨(z : hdata.disk hselected.index),
          hdecomp.protectedTrace_subset_strip z.2⟩ =
        (⟨(φ z : X), frontier_subset_closure (φ z).2⟩ : closure F)
  stripClosureFilling_mem_frontier_on_regionAttachment :
    ∀ (P : hdecomp.piece) (z : hdecomp.region P)
      (hz : (z : hdata.disk hselected.index) ∈ closure hdecomp.strip),
      (stripClosureFilling
          ⟨(z : hdata.disk hselected.index), hz⟩ : X) ∈ frontier F
  stripClosureFilling_mem_chartCover_on_regionAttachment :
    ∀ (P : hdecomp.piece) (z : hdecomp.region P)
      (hz : (z : hdata.disk hselected.index) ∈ closure hdecomp.strip),
      (stripClosureFilling
          ⟨(z : hdata.disk hselected.index), hz⟩ : X) ∈
        ⋃ x ∈ t,
          (smoothBoundary_localBoundaryChartData
            (F := F) hF_smooth (x : X)
            (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
              (F := F) hdata hselected x.2)).neighborhood

/--
%%handwave
name:
  Closed-side replacements for exterior-tracked regions
statement:
  Closed-side region replacement data assigns to each compact complementary
  region left after removing the collar strip a continuous filling into
  \(\overline F\).
-/
structure SelectedExteriorExcursionDiskProtectedTraceClosedSideRegionReplacementData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside)
    (_htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp) :
    Type 1 where
  pieceFilling : ∀ P : hdecomp.piece, C(hdecomp.region P, closure F)

/--
%%handwave
name:
  Closed-side replacements compatible with a fixed strip filling
statement:
  Region replacements are compatible with a fixed closed-side collar-strip
  filling when each replacement agrees with the closed-strip extension on
  boundary overlaps and the replacement fillings agree with each other on
  overlaps of complementary regions.
-/
structure SelectedExteriorExcursionDiskProtectedTraceCompatibleRegionReplacementData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside)
    (htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp)
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp) :
    Type 1 where
  pieceFilling : ∀ P : hdecomp.piece, C(hdecomp.region P, closure F)
  pieceFilling_eqOn_stripClosure :
    ∀ (P : hdecomp.piece)
      (zStrip : closure hdecomp.strip) (zRegion : hdecomp.region P),
      (zStrip : hdata.disk hselected.index) =
          (zRegion : hdata.disk hselected.index) →
        pieceFilling P zRegion = hstrip.stripClosureFilling zStrip
  pieceFilling_eqOn_region :
    ∀ (P Q : hdecomp.piece) (zP : hdecomp.region P)
      (zQ : hdecomp.region Q),
      (zP : hdata.disk hselected.index) =
          (zQ : hdata.disk hselected.index) →
        pieceFilling P zP = pieceFilling Q zQ

/--
%%handwave
name:
  Closed-side replacement data for one complementary region
statement:
  One-region replacement data is a closed-side filling of a single compact
  complementary region, compatible with the closed-strip extension on
  boundary overlaps.
-/
structure SelectedExteriorExcursionDiskProtectedTraceOneRegionReplacementData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside)
    (_htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp)
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp)
    (P : hdecomp.piece) :
    Type 1 where
  pieceFilling : C(hdecomp.region P, closure F)
  pieceFilling_eqOn_stripClosure :
    ∀ (zStrip : closure hdecomp.strip) (zRegion : hdecomp.region P),
      (zStrip : hdata.disk hselected.index) =
          (zRegion : hdata.disk hselected.index) →
        pieceFilling zRegion = hstrip.stripClosureFilling zStrip

/--
%%handwave
name:
  Exterior compression data for one complementary region
statement:
  Exterior compression data for one complementary region records the
  exterior-side map on that region and the fact that it lies outside
  \(\overline F\).
-/
structure SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorCompressionData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    (htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp)
    (P : hdecomp.piece) :
    Type 1 where
  exteriorMap : C(hdecomp.region P, X)
  exteriorMap_eq_tracking :
    ∀ z : hdecomp.region P, exteriorMap z = htracking.exteriorPieceMap P z
  exteriorMap_mapsTo_exterior :
    MapsTo exteriorMap univ (closure F)ᶜ

/--
%%handwave
name:
  Exterior-side tracking gives one-region compression data
statement:
  The exterior-side tracking data supplies exterior compression data for each
  complementary region.
-/
def selectedExteriorExcursionDiskProtectedTrace_oneRegionExteriorCompressionData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    (htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp)
    (P : hdecomp.piece) :
    SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorCompressionData
      (F := F) htracking P where
  exteriorMap := htracking.exteriorPieceMap P
  exteriorMap_eq_tracking := by
    intro z
    rfl
  exteriorMap_mapsTo_exterior := htracking.exteriorPieceMap_mapsTo_exterior P

/--
%%handwave
name:
  Image of a one-region exterior compression
statement:
  The image of a one-region exterior compression is the image of its
  exterior-side map.
-/
def selectedExteriorExcursionDiskProtectedTrace_oneRegionExteriorCompressionImage
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    {htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp}
    {P : hdecomp.piece}
    (hcompression :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorCompressionData
        (F := F) htracking P) :
    Set X :=
  range hcompression.exteriorMap

/--
%%handwave
name:
  A one-region exterior compression has compact image
statement:
  The image of a one-region exterior compression is compact.
proof:
  The complementary region is compact in the selected disk, and the exterior
  compression map is continuous.
-/
theorem selectedExteriorExcursionDiskProtectedTrace_oneRegionExteriorCompressionImage_isCompact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    {htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp}
    {P : hdecomp.piece}
    (hcompression :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorCompressionData
        (F := F) htracking P) :
    IsCompact
      (selectedExteriorExcursionDiskProtectedTrace_oneRegionExteriorCompressionImage
        hcompression) := by
  haveI : CompactSpace (hdecomp.region P) :=
    isCompact_iff_compactSpace.mp (hdecomp.region_compact P)
  simpa [selectedExteriorExcursionDiskProtectedTrace_oneRegionExteriorCompressionImage]
    using (isCompact_univ.image hcompression.exteriorMap.continuous_toFun)

/--
%%handwave
name:
  A one-region exterior compression maps outside the closed side
statement:
  The image of a one-region exterior compression lies in
  \(X\setminus\overline F\).
proof:
  This is part of the exterior-compression data.
-/
theorem selectedExteriorExcursionDiskProtectedTrace_oneRegionExteriorCompressionImage_subset_exterior
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    {htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp}
    {P : hdecomp.piece}
    (hcompression :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorCompressionData
        (F := F) htracking P) :
    selectedExteriorExcursionDiskProtectedTrace_oneRegionExteriorCompressionImage
        hcompression ⊆
      (closure F)ᶜ := by
  rintro x ⟨z, rfl⟩
  exact hcompression.exteriorMap_mapsTo_exterior (by simp)

/--
%%handwave
name:
  One-region attachment to the collar strip
statement:
  The attachment locus of a compact complementary region is the part of that
  region which lies in the closure of the closed-side collar strip.
-/
def selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside)
    (P : hdecomp.piece) :
    Set (hdecomp.region P) :=
  {z | (z : hdata.disk hselected.index) ∈ closure hdecomp.strip}

/--
%%handwave
name:
  One-region attachment is closed
statement:
  The attachment locus of a compact complementary region to the collar strip
  is closed in that region.
proof:
  It is the inverse image of the closed set \(\overline{\text{strip}}\)
  under the inclusion of the region into the selected disk.
-/
theorem selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment_isClosed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside)
    (P : hdecomp.piece) :
    IsClosed
      (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P) := by
  change
    IsClosed
      ((fun z : hdecomp.region P =>
        (z : hdata.disk hselected.index)) ⁻¹' closure hdecomp.strip)
  exact isClosed_closure.preimage continuous_subtype_val

/--
%%handwave
name:
  One-region attachment is compact
statement:
  The attachment locus of a compact complementary region to the collar strip
  is compact.
proof:
  The region is compact by the collar-strip decomposition, and the attachment
  locus is closed in it.
-/
theorem selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment_isCompact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside)
    (P : hdecomp.piece) :
    IsCompact
      (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P) := by
  haveI : CompactSpace (hdecomp.region P) :=
    isCompact_iff_compactSpace.mp (hdecomp.region_compact P)
  exact
    (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment_isClosed
      (F := F) hdecomp P).isCompact

/--
%%handwave
name:
  Closed-side trace on a one-region attachment
statement:
  The closed-side collar-strip filling restricts to a continuous
  \(\overline F\)-valued trace on the attachment locus of a compact
  complementary region.
-/
def selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentTraceMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp)
    (P : hdecomp.piece) :
    C(selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P,
      closure F) where
  toFun := fun z =>
    hstrip.stripClosureFilling
      ⟨((z : hdecomp.region P) : hdata.disk hselected.index), z.2⟩
  continuous_toFun :=
    hstrip.stripClosureFilling.continuous_toFun.comp
      (Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val) _)

/--
%%handwave
name:
  The attachment trace is the closed strip filling
statement:
  At an attachment point, the one-region attachment trace is exactly the
  closed-side strip filling evaluated at the same selected-disk point.
-/
theorem selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentTraceMap_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp)
    (P : hdecomp.piece)
    (z :
      selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P) :
    selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentTraceMap
        (F := F) hstrip P z =
      hstrip.stripClosureFilling
        ⟨((z : hdecomp.region P) : hdata.disk hselected.index), z.2⟩ :=
  rfl

/--
%%handwave
name:
  The one-region attachment trace lies on the frontier
statement:
  The closed-side trace along a one-region attachment circle takes values on
  the frontier of \(F\).
proof:
  This is part of the reflected collar-strip construction: attachment
  circles are the zero-height edge of the collar, and the closed-side strip
  filling sends that edge to the frontier.
-/
theorem selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentTraceMap_mem_frontier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp)
    (P : hdecomp.piece)
    (z :
      selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P) :
    (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentTraceMap
        (F := F) hstrip P z : X) ∈
      frontier F :=
  hstrip.stripClosureFilling_mem_frontier_on_regionAttachment P
    (z : hdecomp.region P) z.2

/--
%%handwave
name:
  Frontier-valued one-region attachment trace
statement:
  The one-region attachment trace is a continuous map from the attachment
  circle to the frontier of \(F\).
-/
def selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp)
    (P : hdecomp.piece) :
    C(selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P,
      frontier F) where
  toFun := fun z =>
    ⟨(selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentTraceMap
        (F := F) hstrip P z : X),
      selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentTraceMap_mem_frontier
        (F := F) hstrip P z⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_subtype_val.comp
        (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentTraceMap
          (F := F) hstrip P).continuous_toFun)
      _

/--
%%handwave
name:
  Frontier attachment trace agrees with the closed-side trace
statement:
  Coercing the frontier-valued attachment trace to \(\overline F\) gives the
  closed-side attachment trace.
-/
theorem selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap_toClosure_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp)
    (P : hdecomp.piece)
    (z :
      selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P) :
    (⟨(selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap
        (F := F) hstrip P z : X),
      frontier_subset_closure
        (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap
          (F := F) hstrip P z).2⟩ : closure F) =
      selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentTraceMap
        (F := F) hstrip P z := by
  apply Subtype.ext
  rfl

/--
%%handwave
name:
  The one-region attachment trace is covered by the smooth collars
statement:
  The frontier-valued trace on a one-region attachment circle lies in the
  finite family of smooth boundary collars used for the protected trace.
proof:
  The closed-side strip filling records that every attachment value of the
  closed strip lies in the finite collar cover.  The frontier-valued
  attachment trace is the same map, with codomain restricted to the frontier.
-/
theorem selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap_mapsTo_chartCover
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp)
    (P : hdecomp.piece) :
    MapsTo
      (fun z :
        selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
          hdecomp P =>
        (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap
          (F := F) hstrip P z : X))
      univ
      (⋃ x ∈ t,
        (smoothBoundary_localBoundaryChartData
          (F := F) hF_smooth (x : X)
          (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
            (F := F) hdata hselected x.2)).neighborhood) := by
  intro z _hz
  simpa [
    selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap,
    selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentTraceMap]
    using hstrip.stripClosureFilling_mem_chartCover_on_regionAttachment
      P (z : hdecomp.region P) z.2

/--
%%handwave
name:
  One-region attachment-trace extension data
statement:
  One-region attachment-trace extension data is a continuous
  \(\overline F\)-valued filling of the compact complementary region whose
  restriction to the attachment locus is the closed-side collar trace.
-/
structure SelectedExteriorExcursionDiskProtectedTraceOneRegionAttachmentTraceExtensionData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside)
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp)
    (P : hdecomp.piece) : Type 1 where
  pieceFilling : C(hdecomp.region P, closure F)
  pieceFilling_eqOn_attachment :
    ∀ z :
      selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P,
      pieceFilling (z : hdecomp.region P) =
        selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentTraceMap
          (F := F) hstrip P z

/--
%%handwave
name:
  Attachment-trace extension data gives a filling
statement:
  One-region attachment-trace extension data immediately gives the
  corresponding \(\overline F\)-valued filling of the compact region.
-/
theorem SelectedExteriorExcursionDiskProtectedTraceOneRegionAttachmentTraceExtensionData.exists_extension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    {hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp}
    {P : hdecomp.piece}
    (hext :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionAttachmentTraceExtensionData
        (F := F) hdecomp hstrip P) :
    ∃ pieceFilling : C(hdecomp.region P, closure F),
      (∀ z :
        selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
          hdecomp P,
        pieceFilling (z : hdecomp.region P) =
          selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentTraceMap
            (F := F) hstrip P z) ∧
      True :=
  ⟨hext.pieceFilling, hext.pieceFilling_eqOn_attachment, trivial⟩

/--
%%handwave
name:
  One-region collar complement is an attached closed disk
statement:
  For a one-region collar-strip decomposition, the remaining compact region
  is a closed parameter disk and its attachment to the collar strip is the
  whole boundary circle of that disk.
proof:
  The collar strips form a finite regular neighborhood of the protected trace
  in the selected closed disk.  In the one-region case, the complementary
  component is a closed disk; the part meeting the closed collar strip is
  exactly its frontier, hence the boundary circle under a disk coordinate.
-/
theorem exists_selectedExteriorExcursionDiskProtectedTrace_oneRegionParameterDiskAttachment
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    (_hF_open : IsOpen F)
    (_hF_compact : IsCompact (closure F))
    (hF_smooth : HasSmoothBoundary F)
    {a b : X} (γ₀ γ₁ : Path a b)
    (H : γ₀.Homotopy γ₁)
    (_hboundary : ∀ z, z ∈ unitSquareBoundary → H z ∈ F)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F))
    (Ψ : C(hdata.disk hselected.index, X))
    (t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected))
    (hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected)
    (hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t)
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside)
    (htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp)
    (P : hdecomp.piece)
    (_hcompression :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorCompressionData
        (F := F) htracking P) :
    ∃ e : hdecomp.region P ≃ₜ Metric.closedBall (0 : ℂ) 1,
      selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
          hdecomp P =
        {z : hdecomp.region P |
          ((e z : Metric.closedBall (0 : ℂ) 1) : ℂ) ∈
            Metric.sphere (0 : ℂ) 1} := by
  refine ⟨hdecomp.regionClosedDiskHomeomorph P, ?_⟩
  simpa [selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment]
    using hdecomp.region_attachment_eq_boundary P

/--
%%handwave
name:
  Attached exterior compression disk data
statement:
  Attached exterior compression disk data records that a compact
  exterior-compressed region is a closed disk, that its attachment locus is
  the boundary circle of that disk.
-/
structure SelectedExteriorExcursionDiskProtectedTraceOneRegionAttachedExteriorCompressionDiskData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    {htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp}
    {P : hdecomp.piece}
    (hcompression :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorCompressionData
        (F := F) htracking P) : Type 1 where
  regionClosedDiskHomeomorph :
    hdecomp.region P ≃ₜ Metric.closedBall (0 : ℂ) 1
  attachment_eq_boundary :
    selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P =
      {z : hdecomp.region P |
        ((regionClosedDiskHomeomorph z :
            Metric.closedBall (0 : ℂ) 1) : ℂ) ∈
          Metric.sphere (0 : ℂ) 1}

/--
%%handwave
name:
  Exterior compression data gives an attached compression disk
statement:
  The one-region exterior compression arising from the finite collar-strip
  decomposition is an attached exterior compression disk.
proof:
  Apply the closed-disk attachment theorem for the one-region collar
  complement.
-/
theorem exists_selectedExteriorExcursionDiskProtectedTrace_oneRegionAttachedExteriorCompressionDiskData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    (hF_open : IsOpen F)
    (hF_compact : IsCompact (closure F))
    (hF_smooth : HasSmoothBoundary F)
    {a b : X} (γ₀ γ₁ : Path a b)
    (H : γ₀.Homotopy γ₁)
    (hboundary : ∀ z, z ∈ unitSquareBoundary → H z ∈ F)
    (hdata : FiniteExteriorExcursionData (F := F) H)
    (hselected : SelectedExteriorExcursionDiskData (F := F) H hdata)
    (φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F))
    (Ψ : C(hdata.disk hselected.index, X))
    (t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected))
    (hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected)
    (hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t)
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside)
    (htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp)
    (P : hdecomp.piece)
    (hcompression :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorCompressionData
        (F := F) htracking P) :
    ∃ _hattached :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionAttachedExteriorCompressionDiskData
        (F := F) hcompression,
      True := by
  rcases
      exists_selectedExteriorExcursionDiskProtectedTrace_oneRegionParameterDiskAttachment
        hF_open hF_compact hF_smooth γ₀ γ₁ H hboundary hdata hselected
        φ Ψ t hcomplex hside hdecomp htracking P hcompression with
    ⟨e, hattachment_eq_boundary⟩
  exact
    ⟨{ regionClosedDiskHomeomorph := e
       attachment_eq_boundary := hattachment_eq_boundary },
      trivial⟩

/--
%%handwave
name:
  Two-sided compression disk data along a one-region attachment
statement:
  Two-sided compression disk data records a common frontier trace on the
  attachment circle, an exterior disk whose boundary is that trace, and the
  fact that the closed-side collar trace has the same boundary values.
-/
structure SelectedExteriorExcursionDiskProtectedTraceOneRegionTwoSidedCompressionDiskData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp)
    {htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp}
    (P : hdecomp.piece)
    (_hcompression :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorCompressionData
        (F := F) htracking P) : Type 1 where
  attachmentTrace :
    C(selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P,
      frontier F)
  exteriorDisk : C(hdecomp.region P, X)
  exteriorDisk_eqOn_attachment :
    ∀ z :
      selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P,
      exteriorDisk (z : hdecomp.region P) = (attachmentTrace z : X)
  exteriorDisk_mapsTo_exterior_off_attachment :
    MapsTo exteriorDisk
      (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P)ᶜ
      (closure F)ᶜ
  closedSideTrace_eq_attachmentTrace :
    ∀ z :
      selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P,
      selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentTraceMap
          (F := F) hstrip P z =
        (⟨(attachmentTrace z : X), frontier_subset_closure (attachmentTrace z).2⟩ :
          closure F)

/--
%%handwave
name:
  Exterior disk data with prescribed attachment trace
statement:
  Exterior boundary disk data is a continuous disk on the complementary
  region, exterior to \(\overline F\) away from the attachment circle, whose
  boundary values are the frontier-valued attachment trace.
-/
structure SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorBoundaryDiskData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp)
    {htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp}
    (P : hdecomp.piece)
    (_hcompression :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorCompressionData
        (F := F) htracking P) : Type 1 where
  exteriorDisk : C(hdecomp.region P, X)
  exteriorDisk_eqOn_attachment :
    ∀ z :
      selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P,
      exteriorDisk (z : hdecomp.region P) =
        (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap
          (F := F) hstrip P z : X)
  exteriorDisk_mapsTo_exterior_off_attachment :
    MapsTo exteriorDisk
      (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
        hdecomp P)ᶜ
      (closure F)ᶜ

/--
%%handwave
name:
  Exterior boundary disk data gives two-sided compression data
statement:
  If a one-region exterior disk has the closed-side frontier trace as its
  boundary and is exterior away from the attachment circle, then it gives
  two-sided compression disk data.
proof:
  Use the frontier-valued closed-side attachment trace as the common trace.
  The exterior boundary disk data gives the exterior boundary equality, and
  coercing that frontier trace to \(\overline F\) gives the closed-side
  attachment trace.
-/
theorem exists_selectedExteriorExcursionDiskProtectedTrace_oneRegionTwoSidedCompressionDiskData_of_exteriorBoundaryDiskData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    {htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp}
    {hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp}
    {P : hdecomp.piece}
    {hcompression :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorCompressionData
        (F := F) htracking P}
    (hexteriorDisk :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorBoundaryDiskData
        (F := F) hstrip P hcompression) :
    ∃ _htwoSided :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionTwoSidedCompressionDiskData
        (F := F) hstrip P hcompression,
      True := by
  let attachmentTrace :
      C(selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
          hdecomp P,
        frontier F) :=
    selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap
      (F := F) hstrip P
  exact
    ⟨{ attachmentTrace := attachmentTrace
       exteriorDisk := hexteriorDisk.exteriorDisk
       exteriorDisk_eqOn_attachment :=
        hexteriorDisk.exteriorDisk_eqOn_attachment
       exteriorDisk_mapsTo_exterior_off_attachment :=
        hexteriorDisk.exteriorDisk_mapsTo_exterior_off_attachment
       closedSideTrace_eq_attachmentTrace := by
        intro z
        exact
          (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap_toClosure_eq
            (F := F) hstrip P z).symm },
      trivial⟩

/--
%%handwave
name:
  Two-sided compression data gives a boundary-matched exterior disk
statement:
  A two-sided compression disk already contains an exterior disk whose
  boundary agrees with the frontier trace determined by the closed-side
  collar strip.
proof:
  The two-sided data says that the exterior disk has the auxiliary frontier
  trace as its boundary and that this auxiliary trace is the same as the
  closed-side strip trace.  Coercing the frontier-valued strip trace to the
  closed side gives that same strip trace, so the two boundary traces agree
  as maps into the surface.
-/
theorem exists_selectedExteriorExcursionDiskProtectedTrace_oneRegionExteriorBoundaryDiskMap_of_twoSidedCompressionDisk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    {htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp}
    {hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp}
    {P : hdecomp.piece}
    {hcompression :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorCompressionData
        (F := F) htracking P}
    (htwoSided :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionTwoSidedCompressionDiskData
        (F := F) hstrip P hcompression) :
    ∃ exteriorDisk : C(hdecomp.region P, X),
      (∀ z :
        selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
          hdecomp P,
        exteriorDisk (z : hdecomp.region P) =
          (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap
            (F := F) hstrip P z : X)) ∧
      MapsTo exteriorDisk
        (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachment
          hdecomp P)ᶜ
        (closure F)ᶜ := by
  refine
    ⟨htwoSided.exteriorDisk, ?_,
      htwoSided.exteriorDisk_mapsTo_exterior_off_attachment⟩
  intro z
  have htrace_closure :
      (⟨(selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap
          (F := F) hstrip P z : X),
        frontier_subset_closure
          (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap
            (F := F) hstrip P z).2⟩ : closure F) =
        (⟨(htwoSided.attachmentTrace z : X),
          frontier_subset_closure (htwoSided.attachmentTrace z).2⟩ :
          closure F) := by
    exact
      (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap_toClosure_eq
        (F := F) hstrip P z).trans
        (htwoSided.closedSideTrace_eq_attachmentTrace z)
  have htrace :
      (selectedExteriorExcursionDiskProtectedTrace_oneRegionStripAttachmentFrontierTraceMap
          (F := F) hstrip P z : X) =
        (htwoSided.attachmentTrace z : X) :=
    congrArg (fun y : closure F => (y : X)) htrace_closure
  exact (htwoSided.exteriorDisk_eqOn_attachment z).trans htrace.symm

/--
%%handwave
name:
  Two-sided compression data supplies exterior boundary disk data
statement:
  A two-sided compression disk supplies the corresponding exterior boundary
  disk data: its exterior disk has the closed-side frontier trace as boundary
  and is exterior to \(\overline F\) away from the attachment circle.
proof:
  Apply the boundary-matched exterior disk map extracted from the two-sided
  data and package the resulting map and its two properties.
-/
theorem exists_selectedExteriorExcursionDiskProtectedTrace_oneRegionExteriorBoundaryDiskData_of_twoSidedCompressionDisk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    {htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp}
    {hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp}
    {P : hdecomp.piece}
    {hcompression :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorCompressionData
        (F := F) htracking P}
    (htwoSided :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionTwoSidedCompressionDiskData
        (F := F) hstrip P hcompression) :
    ∃ _hexteriorDisk :
      SelectedExteriorExcursionDiskProtectedTraceOneRegionExteriorBoundaryDiskData
        (F := F) hstrip P hcompression,
      True := by
  rcases
      exists_selectedExteriorExcursionDiskProtectedTrace_oneRegionExteriorBoundaryDiskMap_of_twoSidedCompressionDisk
        (F := F) htwoSided with
    ⟨exteriorDisk, hboundary_eq, hmaps⟩
  exact
    ⟨{ exteriorDisk := exteriorDisk
       exteriorDisk_eqOn_attachment := hboundary_eq
       exteriorDisk_mapsTo_exterior_off_attachment := hmaps },
      trivial⟩






/--
%%handwave
name:
  Frontier-attached exterior closed disk data
statement:
  Frontier-attached exterior closed disk data consists of a closed disk whose
  boundary circle is attached to the frontier of \(F\), together with a
  continuous disk map which sends the open disk into
  \(X\setminus\overline F\) and agrees on the boundary with the prescribed
  frontier trace.
-/
structure FrontierAttachedExteriorClosedDiskData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X}
    (D : Type) [TopologicalSpace D] [CompactSpace D] : Type 1 where
  diskHomeomorph : D ≃ₜ Metric.closedBall (0 : ℂ) 1
  attachment : Set D
  attachment_eq_boundary :
    attachment =
      {z : D |
        ((diskHomeomorph z : Metric.closedBall (0 : ℂ) 1) : ℂ) ∈
          Metric.sphere (0 : ℂ) 1}
  attachmentTrace : C(attachment, frontier F)
  exteriorDisk : C(D, X)
  exteriorDisk_eqOn_attachment :
    ∀ z : attachment,
      exteriorDisk (z : D) = (attachmentTrace z : X)
  exteriorDisk_mapsTo_exterior_interior :
    MapsTo exteriorDisk
      ({z : D |
        ((diskHomeomorph z : Metric.closedBall (0 : ℂ) 1) : ℂ) ∈
          Metric.ball (0 : ℂ) 1})
      (closure F)ᶜ













/--
%%handwave
name:
  Reflected collar-strip data
statement:
  Reflected collar-strip data records that the finite family of smooth
  boundary collars covering the protected trace has been reflected from the
  exterior side to the closed side, producing a closed-side strip filling.
-/
structure SelectedExteriorExcursionDiskProtectedTraceReflectedCollarStripData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside) :
    Type 1 where
  stripFillingData :
    SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
      (F := F) hdecomp
  stripClosure_covered_by_reflected_charts :
    MapsTo
      (fun z : closure hdecomp.strip => Ψ (z : hdata.disk hselected.index))
      univ
      (⋃ x ∈ t,
        (smoothBoundary_localBoundaryChartData
          (F := F) hF_smooth (x : X)
          (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
            (F := F) hdata hselected x.2)).neighborhood)
  trace_covered_by_reflected_charts :
    MapsTo
      (fun z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected =>
        (φ z : X))
      univ
      (⋃ x ∈ t,
        (smoothBoundary_localBoundaryChartData
          (F := F) hF_smooth (x : X)
          (selectedExteriorExcursionDiskProtectedTraceImage_subset_frontier
            (F := F) hdata hselected x.2)).neighborhood)

/--
%%handwave
name:
  Reflected collar-strip data gives a closed-side strip filling
statement:
  Reflected collar-strip data immediately supplies the closed-side
  collar-strip filling.
-/
def SelectedExteriorExcursionDiskProtectedTraceReflectedCollarStripData.toClosedSideStripFillingData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    (hreflected :
      SelectedExteriorExcursionDiskProtectedTraceReflectedCollarStripData
        (F := F) hdecomp) :
    SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
      (F := F) hdecomp :=
  hreflected.stripFillingData








/--
%%handwave
name:
  Pasted closed-side map data
statement:
  Pasted closed-side map data is a global continuous map from the selected
  parameter disk to \(\overline F\) which agrees with the closed-side collar
  filling on the strip and with the compatible closed-side replacement
  fillings on the complementary regions.
-/
structure SelectedExteriorExcursionDiskProtectedTraceClosedSidePastedMapData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    {htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp}
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp)
    (hreplacements :
      SelectedExteriorExcursionDiskProtectedTraceCompatibleRegionReplacementData
        (F := F) hdecomp htracking hstrip) :
    Type 1 where
  pastedFilling : C(hdata.disk hselected.index, closure F)
  pastedFilling_eqOn_strip :
    ∀ z : hdecomp.strip,
      pastedFilling (z : hdata.disk hselected.index) = hstrip.stripFilling z
  pastedFilling_eqOn_region :
    ∀ (P : hdecomp.piece) (z : hdecomp.region P),
      pastedFilling (z : hdata.disk hselected.index) =
        hreplacements.pieceFilling P z

/--
%%handwave
name:
  Compatible maps on a finite closed cover paste
statement:
  A finite closed cover equipped with continuous maps which agree on all
  overlaps has a unique induced continuous map on the whole space, with the
  prescribed restrictions.
proof:
  Choose, for each point, one closed member of the cover containing it, and
  use the corresponding local value.  The overlap compatibility makes this
  pointwise definition independent of the choice on every cover member.
  Since the cover is finite, it is locally finite; the closed-cover
  continuity theorem then gives continuity of the induced map.
-/
theorem exists_continuousMap_of_finite_closedCover_compatible_subtypeMaps
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {ι : Type*} [Finite ι]
    (s : ι → Set α)
    (hclosed : ∀ i, IsClosed (s i))
    (hcover : (⋃ i, s i) = univ)
    (f : ∀ i, C(s i, β))
    (hcompat :
      ∀ (i j : ι) (xi : s i) (xj : s j),
        (xi : α) = (xj : α) → f i xi = f j xj) :
    ∃ F : C(α, β), ∀ (i : ι) (x : s i), F x = f i x := by
  classical
  let coverExists : ∀ x : α, ∃ i : ι, x ∈ s i := fun x => by
    have hx : x ∈ (⋃ i, s i) := by
      rw [hcover]
      exact mem_univ x
    exact mem_iUnion.mp hx
  let coverIndex : α → ι := fun x => Classical.choose (coverExists x)
  have coverMem : ∀ x : α, x ∈ s (coverIndex x) := fun x =>
    Classical.choose_spec (coverExists x)
  let Ffun : α → β := fun x =>
    f (coverIndex x) ⟨x, coverMem x⟩
  have hFfun_eq : ∀ (i : ι) (x : s i), Ffun x = f i x := by
    intro i x
    exact
      hcompat (coverIndex (x : α)) i
        ⟨(x : α), coverMem (x : α)⟩ x rfl
  have hcontOn : ∀ i : ι, ContinuousOn Ffun (s i) := by
    intro i
    rw [continuousOn_iff_continuous_restrict]
    convert (f i).continuous_toFun using 1
    funext x
    exact hFfun_eq i x
  have hcont : Continuous Ffun :=
    (locallyFinite_of_finite s).continuous hcover hclosed hcontOn
  exact ⟨⟨Ffun, hcont⟩, hFfun_eq⟩

/--
%%handwave
name:
  Finite compatible collar-region cover pasting
statement:
  If the collar strip and the finitely many compact complementary regions
  cover the selected parameter disk, and the closed-side strip filling and
  region replacements agree on all overlaps, then they paste to a continuous
  global \(\overline F\)-valued map.
proof:
  This is the finite topological pasting step.  The strip and the finitely
  many compact remainder regions cover the parameter disk.  On every overlap
  the recorded compatibility equations identify the local maps, so the
  induced pointwise map is well defined.  Finite pasting gives continuity,
  and the construction has the stated restrictions on the strip and on each
  complementary region.
-/
theorem exists_selectedExteriorExcursionDiskProtectedTrace_closedSidePastedMapData_of_pastingCover_and_compatibleFillings
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    {htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp}
    (hcover :
      SelectedExteriorExcursionDiskProtectedTracePastingCoverData
        (F := F) hdecomp)
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp)
    (hreplacements :
      SelectedExteriorExcursionDiskProtectedTraceCompatibleRegionReplacementData
        (F := F) hdecomp htracking hstrip) :
    ∃ _hpasted :
      SelectedExteriorExcursionDiskProtectedTraceClosedSidePastedMapData
        (F := F) hstrip hreplacements,
      True := by
  classical
  letI : Fintype hdecomp.piece := hcover.piece_finite
  let coverSet :
      Option hdecomp.piece → Set (hdata.disk hselected.index)
    | none => closure hdecomp.strip
    | some P => hdecomp.region P
  let coverMap :
      ∀ i : Option hdecomp.piece, C(coverSet i, closure F)
    | none => hstrip.stripClosureFilling
    | some P => hreplacements.pieceFilling P
  have hclosed : ∀ i : Option hdecomp.piece, IsClosed (coverSet i) := by
    intro i
    cases i with
    | none =>
        exact isClosed_closure
    | some P =>
        exact (hcover.region_compact P).isClosed
  have hcover_univ : (⋃ i : Option hdecomp.piece, coverSet i) = univ := by
    ext z
    constructor
    · intro _hz
      exact mem_univ z
    · intro _hz
      by_cases hzStrip : z ∈ hdecomp.strip
      · exact mem_iUnion_of_mem (none : Option hdecomp.piece)
          (subset_closure hzStrip)
      · have hzRegions :
            z ∈ ⋃ P : hdecomp.piece, hdecomp.region P := by
          rw [hcover.regions_eq_strip_compl]
          exact hzStrip
        rcases mem_iUnion.mp hzRegions with ⟨P, hzP⟩
        exact mem_iUnion_of_mem (some P) hzP
  have hcompat :
      ∀ (i j : Option hdecomp.piece) (zi : coverSet i) (zj : coverSet j),
        (zi : hdata.disk hselected.index) =
            (zj : hdata.disk hselected.index) →
          coverMap i zi = coverMap j zj := by
    intro i j zi zj hzij
    cases i with
    | none =>
        cases j with
        | none =>
            have hzz : zi = zj := Subtype.ext hzij
            simp [coverMap, hzz]
        | some Q =>
            exact
              (hreplacements.pieceFilling_eqOn_stripClosure Q zi zj hzij).symm
    | some P =>
        cases j with
        | none =>
            exact
              hreplacements.pieceFilling_eqOn_stripClosure P zj zi hzij.symm
        | some Q =>
            exact
              hreplacements.pieceFilling_eqOn_region P Q zi zj hzij
  rcases
      exists_continuousMap_of_finite_closedCover_compatible_subtypeMaps
        coverSet hclosed hcover_univ coverMap hcompat with
    ⟨pastedFilling, hpasted_eq⟩
  refine
    ⟨{ pastedFilling := pastedFilling
       pastedFilling_eqOn_strip := ?_
       pastedFilling_eqOn_region := ?_ },
      trivial⟩
  · intro z
    calc
      pastedFilling (z : hdata.disk hselected.index)
          = hstrip.stripClosureFilling
              ⟨(z : hdata.disk hselected.index), subset_closure z.2⟩ := by
            simpa [coverSet, coverMap] using
              hpasted_eq (none : Option hdecomp.piece)
                ⟨(z : hdata.disk hselected.index), subset_closure z.2⟩
      _ = hstrip.stripFilling z :=
            hstrip.stripClosureFilling_eqOn_strip z
  · intro P z
    simpa [coverSet, coverMap] using
      hpasted_eq (some P) z

/--
%%handwave
name:
  Finite compatible collar-region pasting gives a global map
statement:
  A closed-side collar-strip filling and compatible closed-side replacements
  on the finitely many complementary regions paste to a global continuous
  \(\overline F\)-valued map on the selected parameter disk.
proof:
  Use the finite cover data supplied by the collar-strip decomposition, and
  then apply the finite compatible collar-region pasting theorem.
-/
theorem exists_selectedExteriorExcursionDiskProtectedTrace_closedSidePastedMapData_of_stripFilling_and_regionReplacements
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    {htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp}
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp)
    (hreplacements :
      SelectedExteriorExcursionDiskProtectedTraceCompatibleRegionReplacementData
        (F := F) hdecomp htracking hstrip) :
    ∃ _hpasted :
      SelectedExteriorExcursionDiskProtectedTraceClosedSidePastedMapData
        (F := F) hstrip hreplacements,
      True := by
  exact
    exists_selectedExteriorExcursionDiskProtectedTrace_closedSidePastedMapData_of_pastingCover_and_compatibleFillings
      (F := F)
      (selectedExteriorExcursionDiskProtectedTrace_pastingCoverData
        (F := F) hdecomp)
      hstrip hreplacements

/--
%%handwave
name:
  Finite collar-region pasting gives compatible closed-side fillings
statement:
  A closed-side collar-strip filling and closed-side fillings of the finitely
  many complementary regions paste to compatible closed-side filling data for
  the selected parameter disk.
proof:
  The strip and the finitely many compact regions form a finite closed-cover
  after taking the recorded collar decomposition.  The collar filling and
  region fillings agree on common frontier arcs by construction: the collar
  value on the protected trace is the prescribed frontier trace, and the
  replacement regions are attached along the same frontier arcs.  The finite
  pasting lemma gives the global \(\overline F\)-valued map and its trace
  agreement.
-/
theorem exists_selectedExteriorExcursionDiskProtectedTrace_closedSidePieceFillingData_of_stripFilling_and_regionReplacements
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    {htracking :
      SelectedExteriorExcursionDiskProtectedTraceExteriorSidePieceTrackingData
        (F := F) hdecomp}
    (hstrip :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideStripFillingData
        (F := F) hdecomp)
    (hreplacements :
      SelectedExteriorExcursionDiskProtectedTraceCompatibleRegionReplacementData
        (F := F) hdecomp htracking hstrip) :
    ∃ _hpieces :
      SelectedExteriorExcursionDiskProtectedTraceClosedSidePieceFillingData
        (F := F) hdecomp,
      True := by
  rcases
      exists_selectedExteriorExcursionDiskProtectedTrace_closedSidePastedMapData_of_stripFilling_and_regionReplacements
        (F := F) hstrip hreplacements with
    ⟨hpasted, _⟩
  refine
    ⟨{ stripFilling := hstrip.stripFilling
       strip_eqOn_trace := hstrip.strip_eqOn_trace
       pieceFilling := hreplacements.pieceFilling
       pastedFilling := hpasted.pastedFilling
       pastedFilling_eqOn_strip := hpasted.pastedFilling_eqOn_strip
       pastedFilling_eqOn_region := hpasted.pastedFilling_eqOn_region
       pastedFilling_eqOn_trace := ?_ },
      trivial⟩
  intro z
  exact
    (hpasted.pastedFilling_eqOn_strip
      ⟨(z : hdata.disk hselected.index),
        hdecomp.protectedTrace_subset_strip z.2⟩).trans
      (hstrip.strip_eqOn_trace z)


/--
%%handwave
name:
  Closed-side extension data for a protected trace
statement:
  Closed-side extension data for a protected trace is a continuous map from
  the selected parameter disk into \(\overline F\) whose restriction to the
  protected trace is the prescribed frontier-valued trace.
-/
structure SelectedExteriorExcursionDiskProtectedTraceClosedSideExtensionData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    (φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F))
    (_Ψ : C(hdata.disk hselected.index, X))
    (_t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected))
    (_hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected)
    (_hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ _Ψ _t) :
    Type 1 where
  filling : C(hdata.disk hselected.index, closure F)
  eqOn_protectedTrace :
    ∀ z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
      filling (z : hdata.disk hselected.index) =
        (⟨(φ z : X), frontier_subset_closure (φ z).2⟩ : closure F)

/--
%%handwave
name:
  Closed-side extension data gives a closed-side extension
statement:
  Closed-side extension data immediately supplies the corresponding
  \(\overline F\)-valued filling of the selected parameter disk.
-/
theorem SelectedExteriorExcursionDiskProtectedTraceClosedSideExtensionData.exists_extension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hclosed :
      SelectedExteriorExcursionDiskProtectedTraceClosedSideExtensionData
        (F := F) φ Ψ t hcomplex hside) :
    ∃ Φ : C(hdata.disk hselected.index, closure F),
      ∀ z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        Φ (z : hdata.disk hselected.index) =
          (⟨(φ z : X), frontier_subset_closure (φ z).2⟩ : closure F) :=
  ⟨hclosed.filling, hclosed.eqOn_protectedTrace⟩

/--
%%handwave
name:
  A closed-side extension map gives closed-side extension data
statement:
  A continuous \(\overline F\)-valued filling of the selected parameter disk
  whose restriction to the protected trace is the prescribed frontier trace
  determines closed-side extension data.
-/
def SelectedExteriorExcursionDiskProtectedTraceClosedSideExtensionData.of_extension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (Φ : C(hdata.disk hselected.index, closure F))
    (hΦ :
      ∀ z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        Φ (z : hdata.disk hselected.index) =
          (⟨(φ z : X), frontier_subset_closure (φ z).2⟩ : closure F)) :
    SelectedExteriorExcursionDiskProtectedTraceClosedSideExtensionData
      (F := F) φ Ψ t hcomplex hside where
  filling := Φ
  eqOn_protectedTrace := hΦ








/--
%%handwave
name:
  Pasting data for the protected trace filling
statement:
  Pasting data is a continuous map from the selected closed disk to
  \(\overline F\) obtained by gluing the collar-strip filling and the
  closed-side fillings of the finitely many complementary pieces.
-/
structure SelectedExteriorExcursionDiskProtectedTracePastingData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    (_hpieces :
      SelectedExteriorExcursionDiskProtectedTraceClosedSidePieceFillingData
        (F := F) hdecomp) :
    Type 1 where
  filling : C(hdata.disk hselected.index, closure F)
  eqOn_protectedTrace :
    ∀ z : selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
      filling (z : hdata.disk hselected.index) =
        (⟨(φ z : X), frontier_subset_closure (φ z).2⟩ : closure F)

/--
%%handwave
name:
  Compatible closed-side fillings give pasting data
statement:
  Compatible closed-side piece-filling data determines the pasted filling of
  the selected disk into \(\overline F\), fixed on the protected trace.
proof:
  The compatible filling data already records the pasted map and its
  agreement with the prescribed frontier trace.
-/
def SelectedExteriorExcursionDiskProtectedTraceClosedSidePieceFillingData.toPastingData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : Set X} {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    {hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside}
    (hpieces :
      SelectedExteriorExcursionDiskProtectedTraceClosedSidePieceFillingData
        (F := F) hdecomp) :
    SelectedExteriorExcursionDiskProtectedTracePastingData
      (F := F) hpieces where
  filling := hpieces.pastedFilling
  eqOn_protectedTrace := hpieces.pastedFilling_eqOn_trace

/--
%%handwave
name:
  Finite cover pasting gives the protected trace filling
statement:
  The collar-strip filling and the finitely many closed-side piece fillings
  paste across the finite collar-strip cover to a continuous filling of the
  selected closed disk into \(\overline F\), fixed on the protected trace.
proof:
  The finite cover data has already been used in the construction of the
  compatible closed-side filling data.  That data records the pasted filling
  and its trace agreement, so package it as pasting data.
-/
theorem exists_selectedExteriorExcursionDiskProtectedTrace_pastingData_of_pastingCover_and_pieceFillings
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside)
    (hpieces :
      SelectedExteriorExcursionDiskProtectedTraceClosedSidePieceFillingData
        (F := F) hdecomp)
    (_hcover :
      SelectedExteriorExcursionDiskProtectedTracePastingCoverData
        (F := F) hdecomp) :
    ∃ _hpasting :
      SelectedExteriorExcursionDiskProtectedTracePastingData
        (F := F) hpieces,
      True := by
  exact ⟨hpieces.toPastingData, trivial⟩

/--
%%handwave
name:
  Finite pasting gives the protected trace filling
statement:
  The collar-strip filling and the finitely many closed-side piece fillings
  paste to a continuous filling of the selected closed disk into
  \(\overline F\), fixed on the protected trace.
proof:
  First extract the finite cover data from the collar-strip decomposition.
  Then apply finite cover pasting to the strip filling and the closed-side
  piece fillings.
-/
theorem exists_selectedExteriorExcursionDiskProtectedTrace_pastingData_of_collarStripDecomposition_and_pieceFillings
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    {hF_smooth : HasSmoothBoundary F}
    {a b : X} {γ₀ γ₁ : Path a b}
    {H : γ₀.Homotopy γ₁}
    {hdata : FiniteExteriorExcursionData (F := F) H}
    {hselected : SelectedExteriorExcursionDiskData (F := F) H hdata}
    {φ :
      C(selectedExteriorExcursionDiskProtectedTraceSet hdata hselected,
        frontier F)}
    {Ψ : C(hdata.disk hselected.index, X)}
    {t :
      Finset
        (selectedExteriorExcursionDiskProtectedTraceImage
          (F := F) H hdata hselected)}
    {hcomplex :
      SelectedExteriorExcursionDiskProtectedTraceFiniteBoundaryComplexData
        (F := F) hdata hselected}
    {hside :
      SelectedExteriorExcursionDiskProtectedTraceCollarSideData
        (F := F) hF_smooth H hdata hselected φ Ψ t}
    (hdecomp :
      SelectedExteriorExcursionDiskProtectedTraceCollarStripDecompositionData
        (F := F) hF_smooth H hdata hselected φ Ψ t hcomplex hside)
    (hpieces :
      SelectedExteriorExcursionDiskProtectedTraceClosedSidePieceFillingData
        (F := F) hdecomp) :
    ∃ _hpasting :
      SelectedExteriorExcursionDiskProtectedTracePastingData
        (F := F) hpieces,
      True := by
  exact
    exists_selectedExteriorExcursionDiskProtectedTrace_pastingData_of_pastingCover_and_pieceFillings
      (F := F) hdecomp hpieces
      (selectedExteriorExcursionDiskProtectedTrace_pastingCoverData
        (F := F) hdecomp)



























/--
%%handwave
name:
  Local frontier collar data
statement:
  At a parameter point mapping to the smooth frontier of \(F\), a local
  collar datum records a smooth boundary chart, a defining function with
  nonzero derivative, and a small parameter neighborhood that maps into this
  chart and lies away from the square boundary.
-/
structure LocalFrontierCollarPushData {X : Type} [TopologicalSpace X]
    [ChartedSpace ℂ X]
    {F : Set X} {a b : X} {γ₀ γ₁ : Path a b}
    (H : γ₀.Homotopy γ₁) (z : unitInterval × unitInterval) : Type where
  chart : OpenPartialHomeomorph X ℂ
  chart_mem_atlas : chart ∈ atlas ℂ X
  image_mem_source : H z ∈ chart.source
  definingFunction : ℂ → ℝ
  definingFunction_smooth :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) definingFunction (chart (H z))
  definingDerivative : ℂ →L[ℝ] ℝ
  definingFunction_deriv :
    HasFDerivAt definingFunction definingDerivative (chart (H z))
  definingDerivative_ne_zero : definingDerivative ≠ 0
  local_boundary_model :
    ∀ᶠ y in 𝓝 (H z),
      y ∈ chart.source ∧
        (y ∈ F ↔ definingFunction (chart y) < 0) ∧
          (y ∈ frontier F ↔ definingFunction (chart y) = 0)
  neighborhood : Set (unitInterval × unitInterval)
  isOpen_neighborhood : IsOpen neighborhood
  mem_neighborhood : z ∈ neighborhood
  subset_squareInterior : neighborhood ⊆ unitSquareBoundaryᶜ
  mapsTo_chart_source : MapsTo H neighborhood chart.source

/--
%%handwave
name:
  Smooth frontiers have local one-sided collar data
statement:
  Let \(F\) be an open smooth-boundary relatively compact subsurface, and let
  a closure-valued homotopy send a parameter point to the frontier of \(F\).
  If the frontier preimage is disjoint from the square boundary, then that
  parameter point has a smooth one-sided collar neighborhood supported inside
  the interior of the square.
proof:
  Choose a smooth boundary chart at the image frontier point.  In that chart
  \(F\) is one side of a straight interval.  Since the parameter point lies
  away from the square boundary, shrink the parameter neighborhood so that it
  remains in the square interior and its image lies in the boundary chart.
-/
theorem exists_smoothRelativelyCompactOpen_localFrontierCollarPushData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    (_hF_open : IsOpen F)
    (_hF_compact : IsCompact (closure F))
    (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (Hc : γ₀.Homotopy γ₁)
    (_hHc_closure : ∀ z, Hc z ∈ closure F)
    (hFrontier_interior :
      pathHomotopyFrontierPreimage (F := F) Hc ⊆ unitSquareBoundaryᶜ)
    (z : unitInterval × unitInterval)
    (hz : z ∈ pathHomotopyFrontierPreimage (F := F) Hc) :
    ∃ _hdata : LocalFrontierCollarPushData (F := F) Hc z, True := by
  rcases hF_smooth (Hc z) hz with
    ⟨e, he_atlas, he_source, r, hr_smooth, dr, hr_deriv, hdr_ne, hlocal⟩
  let N : Set (unitInterval × unitInterval) :=
    unitSquareBoundaryᶜ ∩ Hc ⁻¹' e.source
  have hN_open : IsOpen N := by
    exact unitSquareBoundary_isOpen_compl.inter
      (e.open_source.preimage (ContinuousMap.HomotopyWith.continuous Hc))
  have hzN : z ∈ N := by
    exact ⟨hFrontier_interior hz, he_source⟩
  refine ⟨?_, trivial⟩
  exact
    { chart := e
      chart_mem_atlas := he_atlas
      image_mem_source := he_source
      definingFunction := r
      definingFunction_smooth := hr_smooth.contDiffAt
      definingDerivative := dr
      definingFunction_deriv := hr_deriv
      definingDerivative_ne_zero := hdr_ne
      local_boundary_model := hlocal
      neighborhood := N
      isOpen_neighborhood := hN_open
      mem_neighborhood := hzN
      subset_squareInterior := by
        intro y hy
        exact hy.1
      mapsTo_chart_source := by
        intro y hy
        exact hy.2 }

/--
%%handwave
name:
  Chosen local frontier collar data
statement:
  Choose the local one-sided collar datum at a frontier parameter point.
-/
noncomputable def smoothRelativelyCompactOpen_localFrontierCollarPushData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    (hF_open : IsOpen F)
    (hF_compact : IsCompact (closure F))
    (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (Hc : γ₀.Homotopy γ₁)
    (hHc_closure : ∀ z, Hc z ∈ closure F)
    (hFrontier_interior :
      pathHomotopyFrontierPreimage (F := F) Hc ⊆ unitSquareBoundaryᶜ)
    (z : unitInterval × unitInterval)
    (hz : z ∈ pathHomotopyFrontierPreimage (F := F) Hc) :
    LocalFrontierCollarPushData (F := F) Hc z :=
  (exists_smoothRelativelyCompactOpen_localFrontierCollarPushData
    hF_open hF_compact hF_smooth Hc hHc_closure
    hFrontier_interior z hz).choose

/--
%%handwave
name:
  Compact frontier-preimages have finite collar covers
statement:
  If the frontier preimage of a closure-valued homotopy is compact and lies
  away from the square boundary, then finitely many local smooth collar
  neighborhoods cover it.
proof:
  Apply compactness to the open cover by the chosen local collar
  neighborhoods.
-/
theorem smoothRelativelyCompactOpen_finiteLocalFrontierCollarCover
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    (hF_open : IsOpen F)
    (hF_compact : IsCompact (closure F))
    (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (Hc : γ₀.Homotopy γ₁)
    (hHc_closure : ∀ z, Hc z ∈ closure F)
    (hFrontier_compact :
      IsCompact (pathHomotopyFrontierPreimage (F := F) Hc))
    (hFrontier_interior :
      pathHomotopyFrontierPreimage (F := F) Hc ⊆ unitSquareBoundaryᶜ) :
    ∃ t : Finset (pathHomotopyFrontierPreimage (F := F) Hc),
      pathHomotopyFrontierPreimage (F := F) Hc ⊆
        ⋃ z ∈ t,
          (smoothRelativelyCompactOpen_localFrontierCollarPushData
            hF_open hF_compact hF_smooth Hc hHc_closure
            hFrontier_interior z z.2).neighborhood := by
  let U : (pathHomotopyFrontierPreimage (F := F) Hc) →
      Set (unitInterval × unitInterval) := fun z =>
    (smoothRelativelyCompactOpen_localFrontierCollarPushData
      hF_open hF_compact hF_smooth Hc hHc_closure
      hFrontier_interior z z.2).neighborhood
  have hU_open : ∀ z, IsOpen (U z) := by
    intro z
    exact
      (smoothRelativelyCompactOpen_localFrontierCollarPushData
        hF_open hF_compact hF_smooth Hc hHc_closure
        hFrontier_interior z z.2).isOpen_neighborhood
  have hcover :
      pathHomotopyFrontierPreimage (F := F) Hc ⊆ ⋃ z, U z := by
    intro y hy
    exact
      mem_iUnion_of_mem ⟨y, hy⟩
        (smoothRelativelyCompactOpen_localFrontierCollarPushData
          hF_open hF_compact hF_smooth Hc hHc_closure
          hFrontier_interior y hy).mem_neighborhood
  rcases hFrontier_compact.elim_finite_subcover U hU_open hcover with
    ⟨t, ht⟩
  exact ⟨t, by simpa [U] using ht⟩

/--
%%handwave
name:
  Finite collar-cover support
statement:
  The support associated to a finite family of local frontier collars is the
  union of their parameter neighborhoods.
-/
noncomputable def smoothRelativelyCompactOpen_finiteLocalFrontierCollarSupport
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    (hF_open : IsOpen F)
    (hF_compact : IsCompact (closure F))
    (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (Hc : γ₀.Homotopy γ₁)
    (hHc_closure : ∀ z, Hc z ∈ closure F)
    (hFrontier_interior :
      pathHomotopyFrontierPreimage (F := F) Hc ⊆ unitSquareBoundaryᶜ)
    (t : Finset (pathHomotopyFrontierPreimage (F := F) Hc)) :
    Set (unitInterval × unitInterval) :=
  ⋃ z ∈ t,
    (smoothRelativelyCompactOpen_localFrontierCollarPushData
      hF_open hF_compact hF_smooth Hc hHc_closure
      hFrontier_interior z z.2).neighborhood

/--
%%handwave
name:
  Finite collar-cover supports are open
statement:
  The support associated to a finite family of local frontier collars is open.
proof:
  It is a union of open parameter neighborhoods.
-/
theorem smoothRelativelyCompactOpen_finiteLocalFrontierCollarSupport_isOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    (hF_open : IsOpen F)
    (hF_compact : IsCompact (closure F))
    (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (Hc : γ₀.Homotopy γ₁)
    (hHc_closure : ∀ z, Hc z ∈ closure F)
    (hFrontier_interior :
      pathHomotopyFrontierPreimage (F := F) Hc ⊆ unitSquareBoundaryᶜ)
    (t : Finset (pathHomotopyFrontierPreimage (F := F) Hc)) :
    IsOpen
      (smoothRelativelyCompactOpen_finiteLocalFrontierCollarSupport
        hF_open hF_compact hF_smooth Hc hHc_closure
        hFrontier_interior t) := by
  dsimp [smoothRelativelyCompactOpen_finiteLocalFrontierCollarSupport]
  exact isOpen_iUnion fun z =>
    isOpen_iUnion fun _hz =>
      (smoothRelativelyCompactOpen_localFrontierCollarPushData
        hF_open hF_compact hF_smooth Hc hHc_closure
        hFrontier_interior z z.2).isOpen_neighborhood

/--
%%handwave
name:
  Finite collar-cover supports contain the frontier preimage
statement:
  If a finite collar family covers the frontier preimage, then its support
  contains the frontier preimage.
-/
theorem smoothRelativelyCompactOpen_frontierPreimage_subset_finiteLocalFrontierCollarSupport
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    (hF_open : IsOpen F)
    (hF_compact : IsCompact (closure F))
    (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (Hc : γ₀.Homotopy γ₁)
    (hHc_closure : ∀ z, Hc z ∈ closure F)
    (hFrontier_interior :
      pathHomotopyFrontierPreimage (F := F) Hc ⊆ unitSquareBoundaryᶜ)
    (t : Finset (pathHomotopyFrontierPreimage (F := F) Hc))
    (hcover :
      pathHomotopyFrontierPreimage (F := F) Hc ⊆
        ⋃ z ∈ t,
          (smoothRelativelyCompactOpen_localFrontierCollarPushData
            hF_open hF_compact hF_smooth Hc hHc_closure
            hFrontier_interior z z.2).neighborhood) :
    pathHomotopyFrontierPreimage (F := F) Hc ⊆
      smoothRelativelyCompactOpen_finiteLocalFrontierCollarSupport
        hF_open hF_compact hF_smooth Hc hHc_closure
        hFrontier_interior t := by
  simpa [smoothRelativelyCompactOpen_finiteLocalFrontierCollarSupport] using hcover

/--
%%handwave
name:
  Finite collar-cover supports lie in the square interior
statement:
  The support associated to a finite family of local frontier collars lies
  away from the boundary of the parameter square.
proof:
  Each local collar neighborhood was chosen inside the square interior.
-/
theorem smoothRelativelyCompactOpen_finiteLocalFrontierCollarSupport_subset_squareInterior
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    (hF_open : IsOpen F)
    (hF_compact : IsCompact (closure F))
    (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (Hc : γ₀.Homotopy γ₁)
    (hHc_closure : ∀ z, Hc z ∈ closure F)
    (hFrontier_interior :
      pathHomotopyFrontierPreimage (F := F) Hc ⊆ unitSquareBoundaryᶜ)
    (t : Finset (pathHomotopyFrontierPreimage (F := F) Hc)) :
    smoothRelativelyCompactOpen_finiteLocalFrontierCollarSupport
      hF_open hF_compact hF_smooth Hc hHc_closure
      hFrontier_interior t ⊆ unitSquareBoundaryᶜ := by
  intro y hy
  simp only [smoothRelativelyCompactOpen_finiteLocalFrontierCollarSupport,
    mem_iUnion] at hy
  rcases hy with ⟨z, hz⟩
  rcases hz with ⟨_hzt, hyz⟩
  exact
    (smoothRelativelyCompactOpen_localFrontierCollarPushData
      hF_open hF_compact hF_smooth Hc hHc_closure
      hFrontier_interior z z.2).subset_squareInterior hyz

/--
%%handwave
name:
  A finite collar family supporting a nonempty frontier is nonempty
statement:
  If the frontier preimage is nonempty and a supported push weight has
  support equal to the finite union of local frontier collars, then the
  finite collar family is nonempty.
proof:
  A supported push weight contains the whole frontier preimage in its
  support.  If the finite collar family were empty, that support would be
  empty, contradicting the chosen frontier point.
-/
theorem smoothRelativelyCompactOpen_finiteLocalFrontierCollarSupport_cover_ne_empty_of_frontier_nonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : Set X}
    (hF_open : IsOpen F)
    (hF_compact : IsCompact (closure F))
    (hF_smooth : HasSmoothBoundary F)
    {a b : X} {γ₀ γ₁ : Path a b}
    (Hc : γ₀.Homotopy γ₁)
    (hHc_closure : ∀ z, Hc z ∈ closure F)
    (hFrontier_interior :
      pathHomotopyFrontierPreimage (F := F) Hc ⊆ unitSquareBoundaryᶜ)
    (hFrontier_nonempty :
      (pathHomotopyFrontierPreimage (F := F) Hc).Nonempty)
    (t : Finset (pathHomotopyFrontierPreimage (F := F) Hc))
    (support : Set (unitInterval × unitInterval))
    (hsupport_eq :
      support =
        smoothRelativelyCompactOpen_finiteLocalFrontierCollarSupport
          hF_open hF_compact hF_smooth Hc hHc_closure
          hFrontier_interior t)
    (supportedWeightData :
      PathHomotopySupportedFrontierPushWeightData
        (F := F) Hc support) :
    t ≠ ∅ := by
  intro ht
  rcases hFrontier_nonempty with ⟨z, hz⟩
  have hzsupport : z ∈ support :=
    supportedWeightData.frontier_subset_support hz
  rw [hsupport_eq, ht] at hzsupport
  simp [smoothRelativelyCompactOpen_finiteLocalFrontierCollarSupport] at hzsupport

/--
%%handwave
name:
  Supported finite collar deformation data
statement:
  Supported finite collar deformation data is a homotopy between the original
  two paths whose image lies in \(F\).
-/
structure SmoothRelativelyCompactOpenSupportedFiniteCollarDeformationData
    {X : Type} [TopologicalSpace X]
    {F : Set X} {a b : X} (γ₀ γ₁ : Path a b) : Type 1 where
  homotopy : γ₀.Homotopy γ₁
  mapsTo_open : ∀ z, homotopy z ∈ F

/--
%%handwave
name:
  Supported finite collar deformation data gives an open-side homotopy
statement:
  Supported finite collar deformation data immediately gives a homotopy
  between the original paths whose image lies in \(F\).
-/
theorem SmoothRelativelyCompactOpenSupportedFiniteCollarDeformationData.exists_homotopy
    {X : Type} [TopologicalSpace X]
    {F : Set X} {a b : X} {γ₀ γ₁ : Path a b}
    (hdata :
      SmoothRelativelyCompactOpenSupportedFiniteCollarDeformationData
        (F := F) γ₀ γ₁) :
    ∃ H' : γ₀.Homotopy γ₁, ∀ z, H' z ∈ F :=
  ⟨hdata.homotopy, hdata.mapsTo_open⟩




















end Uniformization

end JJMath
