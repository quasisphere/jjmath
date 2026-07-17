import JJMath.Uniformization.EscapingAtlasVortexTransport
import JJMath.Uniformization.PuncturedAngularForm
import JJMath.Uniformization.SurfaceEndPath
import JJMath.Manifold.CirclePrimitiveUniqueness

/-!
# A punctured circle primitive from an exterior component

Nested exterior components of a smooth exhaustion provide the escaping open
sets required by the blockwise atlas-vortex telescope.  This produces a
smooth unit phase, and hence its canonical circle primitive, on the surface
with one point removed.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

noncomputable section

/-- If a compact set contains the puncture and has an exterior component,
the exterior component can absorb the compensating vortex through a smooth
exhaustion.  The limiting unit phase on the punctured surface has a circle
primitive. -/
theorem IsExteriorComponent.exists_circlePrimitive_on_puncturedSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (E : SmoothRelativelyCompactExhaustion X)
    {K V : Set X} (hKcompact : IsCompact K)
    (hV : IsExteriorComponent K V) {p : X} (hpK : p ∈ K) :
    ∃ (P : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
          (atlasVortexInitialOpen p) ℂ ∞)
        (hP : ∀ z : atlasVortexInitialOpen p, ‖P z‖ = 1),
      Nonempty (JJMath.Manifold.SmoothCirclePrimitive SurfaceRealModel
        (smoothUnitPhaseOneForm SurfaceRealModel P hP)) := by
  classical
  rcases hV.exists_nested_sequence_along_smoothExhaustion E hKcompact with
    ⟨N, U, hK, hUexterior, _hU0V, hUsucc⟩
  have hUanti : Antitone U := antitone_nat_of_succ_le hUsucc
  let W : ℕ → TopologicalSpace.Opens X := fun n =>
    ⟨U n, (hUexterior n).isComponentOf.isOpen_of_isOpen
      isClosed_closure.isOpen_compl⟩
  let v : ℕ → X := fun n => Classical.choose (hUexterior n).nonempty
  have hv : ∀ n, v n ∈ U n := fun n =>
    Classical.choose_spec (hUexterior n).nonempty
  have hchain : ∀ n,
      AtlasVortexChainJoinedIn (W n) (v n) (v (n + 1)) := by
    intro n
    letI : ConnectedSpace (W n) := isConnected_iff_connectedSpace.mp (by
      simpa [W] using (hUexterior n).isComponentOf.isConnected)
    exact atlasVortexChainJoinedIn_all (W n)
      ⟨v n, by simpa [W] using hv n⟩
      ⟨v (n + 1), by
        simpa [W] using hUanti (Nat.le_succ n) (hv (n + 1))⟩
  let path : ∀ n,
      ControlledAtlasVortexPath (W n) (v n) (v (n + 1)) := fun n =>
    Classical.choice
      (ControlledAtlasVortexPath.nonempty_of_joined
        (by simpa [W] using hv n) (hchain n))
  have hpU0 : p ∉ U 0 := by
    intro hpU
    exact (hUexterior 0).subset_compl hpU (hK hpK)
  have hpv0 : p ≠ v 0 := by
    intro hpv
    apply hpU0
    rw [hpv]
    exact hv 0
  let A : TopologicalSpace.Opens X := ⊤
  letI : ConnectedSpace A := isConnected_iff_connectedSpace.mp (by
    simpa [A] using (isConnected_univ : IsConnected (Set.univ : Set X)))
  have hinitialJoined : AtlasVortexChainJoinedIn A p (v 0) :=
    atlasVortexChainJoinedIn_all A
      ⟨p, by simp [A]⟩ ⟨v 0, by simp [A]⟩
  let initialPath : ControlledAtlasVortexPath A p (v 0) :=
    Classical.choice
      (ControlledAtlasVortexPath.nonempty_of_joined (by simp [A]) hinitialJoined)
  let T₀ : AtlasVortexTransportData X p (v 0) :=
    Classical.choice (initialPath.nonempty_transport hpv0)
  have hpW : ∀ n, p ∉ W n := by
    intro n hpUn
    apply hpU0
    exact hUanti (Nat.zero_le n) (by simpa [W] using hpUn)
  have hescape : ∀ z : atlasVortexInitialOpen p,
      ∃ n₀ : ℕ, ∃ O : TopologicalSpace.Opens (atlasVortexInitialOpen p),
        z ∈ O ∧ ∀ n ≥ n₀, ∀ y ∈ O, (y : X) ∉ W n := by
    intro z
    rcases E.exhausts (z : X) with ⟨k, hzk⟩
    let O : TopologicalSpace.Opens (atlasVortexInitialOpen p) :=
      ⟨{y | (y : X) ∈ (E.domain k).carrier},
        (E.domain k).isOpen.preimage
          (continuous_subtype_val : Continuous
            (fun y : atlasVortexInitialOpen p ↦ (y : X)))⟩
    refine ⟨k, O, hzk, ?_⟩
    intro n hkn y hyO hyW
    have hindex : k ≤ N + n := hkn.trans (Nat.le_add_left n N)
    have hyLate : (y : X) ∈ (E.domain (N + n)).carrier :=
      smoothRelativelyCompactExhaustion_carrier_mono E hindex hyO
    have hyClosure : (y : X) ∈ closure (E.domain (N + n)).carrier :=
      subset_closure hyLate
    exact (hUexterior n).subset_compl (by simpa [W] using hyW) hyClosure
  exact exists_circlePrimitive_of_locallyEscaping_controlledAtlasVortexPaths
    p W v path T₀ hpW hescape

/-- Starting from any finite transport whose terminal point lies in the
chosen exterior component, the escaping telescope preserves that transport
exactly on the non-exterior side. -/
theorem IsExteriorComponent.exists_circlePrimitive_on_puncturedSurface_of_initialTransport
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (E : SmoothRelativelyCompactExhaustion X)
    {K V : Set X} (hKcompact : IsCompact K)
    (hV : IsExteriorComponent K V) {p q : X} (hpK : p ∈ K)
    (hqV : q ∈ V) (Tinit : AtlasVortexTransportData X p q) :
    ∃ (P : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
          (atlasVortexInitialOpen p) ℂ ∞)
        (hP : ∀ z : atlasVortexInitialOpen p, ‖P z‖ = 1),
      Nonempty (JJMath.Manifold.SmoothCirclePrimitive SurfaceRealModel
          (smoothUnitPhaseOneForm SurfaceRealModel P hP)) ∧
        ∀ (z : coordinateVortexPairOpen p q), (z : X) ∉ V →
          P ⟨(z : X), z.2.1⟩ = Tinit.phase z := by
  classical
  rcases hV.exists_nested_sequence_along_smoothExhaustion E hKcompact with
    ⟨N, U, _hK, hUexterior, hU0V, hUsucc⟩
  have hUanti : Antitone U := antitone_nat_of_succ_le hUsucc
  let W : ℕ → TopologicalSpace.Opens X := fun n =>
    ⟨U n, (hUexterior n).isComponentOf.isOpen_of_isOpen
      isClosed_closure.isOpen_compl⟩
  let v : ℕ → X := fun n => Classical.choose (hUexterior n).nonempty
  have hv : ∀ n, v n ∈ U n := fun n =>
    Classical.choose_spec (hUexterior n).nonempty
  have hchain : ∀ n,
      AtlasVortexChainJoinedIn (W n) (v n) (v (n + 1)) := by
    intro n
    letI : ConnectedSpace (W n) := isConnected_iff_connectedSpace.mp (by
      simpa [W] using (hUexterior n).isComponentOf.isConnected)
    exact atlasVortexChainJoinedIn_all (W n)
      ⟨v n, by simpa [W] using hv n⟩
      ⟨v (n + 1), by
        simpa [W] using hUanti (Nat.le_succ n) (hv (n + 1))⟩
  let path : ∀ n,
      ControlledAtlasVortexPath (W n) (v n) (v (n + 1)) := fun n =>
    Classical.choice
      (ControlledAtlasVortexPath.nonempty_of_joined
        (by simpa [W] using hv n) (hchain n))
  have hpV : p ∉ V := by
    intro hpV
    exact hV.subset_compl hpV hpK
  let WV : TopologicalSpace.Opens X :=
    ⟨V, hV.isComponentOf.isOpen_of_isOpen hKcompact.isClosed.isOpen_compl⟩
  letI : ConnectedSpace WV := isConnected_iff_connectedSpace.mp (by
    simpa [WV] using hV.isComponentOf.isConnected)
  have hv0V : v 0 ∈ V := hU0V (hv 0)
  have hinitialJoined : AtlasVortexChainJoinedIn WV q (v 0) :=
    atlasVortexChainJoinedIn_all WV
      ⟨q, by simpa [WV] using hqV⟩ ⟨v 0, by simpa [WV] using hv0V⟩
  let initialPath : ControlledAtlasVortexPath WV q (v 0) :=
    Classical.choice
      (ControlledAtlasVortexPath.nonempty_of_joined
        (by simpa [WV] using hqV) hinitialJoined)
  rcases initialPath.exists_append_transport Tinit (by simpa [WV] using hpV) with
    ⟨T₀, hT₀⟩
  have hpW : ∀ n, p ∉ W n := by
    intro n hpUn
    apply hpV
    exact hU0V (hUanti (Nat.zero_le n) (by simpa [W] using hpUn))
  have hescape : ∀ z : atlasVortexInitialOpen p,
      ∃ n₀ : ℕ, ∃ O : TopologicalSpace.Opens (atlasVortexInitialOpen p),
        z ∈ O ∧ ∀ n ≥ n₀, ∀ y ∈ O, (y : X) ∉ W n := by
    intro z
    rcases E.exhausts (z : X) with ⟨k, hzk⟩
    let O : TopologicalSpace.Opens (atlasVortexInitialOpen p) :=
      ⟨{y | (y : X) ∈ (E.domain k).carrier},
        (E.domain k).isOpen.preimage
          (continuous_subtype_val : Continuous
            (fun y : atlasVortexInitialOpen p ↦ (y : X)))⟩
    refine ⟨k, O, hzk, ?_⟩
    intro n hkn y hyO hyW
    have hindex : k ≤ N + n := hkn.trans (Nat.le_add_left n N)
    have hyLate : (y : X) ∈ (E.domain (N + n)).carrier :=
      smoothRelativelyCompactExhaustion_carrier_mono E hindex hyO
    have hyClosure : (y : X) ∈ closure (E.domain (N + n)).carrier :=
      subset_closure hyLate
    exact (hUexterior n).subset_compl (by simpa [W] using hyW) hyClosure
  rcases
      exists_circlePrimitive_of_locallyEscaping_controlledAtlasVortexPaths_with_stability
        p W v path T₀ hpW hescape with
    ⟨P, hP, hstable, hprimitive⟩
  refine ⟨P, hP, hprimitive, ?_⟩
  intro z hzV
  let zP : atlasVortexInitialOpen p := ⟨(z : X), z.2.1⟩
  have hzW : ∀ n, (zP : X) ∉ W n := by
    intro n hzUn
    apply hzV
    exact hU0V (hUanti (Nat.zero_le n) (by simpa [W, zP] using hzUn))
  have hzvn : ∀ n, (z : X) ≠ v n := by
    intro n hz
    apply hzV
    rw [hz]
    exact hU0V (hUanti (Nat.zero_le n) (hv n))
  have hpartial : ∀ n,
      controlledAtlasVortexPathTransportPartialPhase
          p W v path T₀ hpW n zP =
        controlledAtlasVortexPathTransportPartialPhase
          p W v path T₀ hpW 0 zP := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        exact (controlledAtlasVortexPathTransportPartialPhase_succ_eq
          p W v path T₀ hpW n zP (hzW n)).trans ih
  rcases hstable zP with ⟨m, hm⟩
  calc
    P zP = controlledAtlasVortexPathTransportPartialPhase
        p W v path T₀ hpW m zP := hm m le_rfl
    _ = controlledAtlasVortexPathTransportPartialPhase
        p W v path T₀ hpW 0 zP := hpartial m
    _ = T₀.phase
        (⟨(z : X), ⟨z.2.1, hzvn 0⟩⟩ :
          coordinateVortexPairOpen p (v 0)) := by
      simp [controlledAtlasVortexPathTransportPartialPhase,
        controlledAtlasVortexPathTransport, zP, hzvn 0]
    _ = Tinit.phase z := by
      simpa [WV] using hT₀
        (⟨(z : X), ⟨z.2.1, hzvn 0⟩⟩ :
          coordinateVortexPairOpen p (v 0)) hzV

/-- A prescribed compact atlas vortex can be transported to infinity while
its phase is left unchanged on the non-exterior side. -/
theorem IsExteriorComponent.exists_circlePrimitive_extending_atlasVortex
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (E : SmoothRelativelyCompactExhaustion X)
    {K V : Set X} (hKcompact : IsCompact K)
    (hV : IsExteriorComponent K V) {p q : X} (hpK : p ∈ K)
    (hqV : q ∈ V) (D : AtlasVortexPairData X p q) :
    ∃ (P : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
          (atlasVortexInitialOpen p) ℂ ∞)
        (hP : ∀ z : atlasVortexInitialOpen p, ‖P z‖ = 1),
      Nonempty (JJMath.Manifold.SmoothCirclePrimitive SurfaceRealModel
          (smoothUnitPhaseOneForm SurfaceRealModel P hP)) ∧
        ∀ (z : coordinateVortexPairOpen p q), (z : X) ∉ V →
          P ⟨(z : X), z.2.1⟩ = D.globalPhase z := by
  simpa using hV.exists_circlePrimitive_on_puncturedSurface_of_initialTransport
    E hKcompact hpK hqV (AtlasVortexTransportData.single D)

/-- Every compact atlas vortex based at the puncture can be transported to
infinity while remaining literally unchanged on a coordinate neighborhood of
the puncture. -/
theorem AtlasVortexPairData.exists_globalCirclePrimitive_preserving_local
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (D : AtlasVortexPairData X p q) :
    ∃ K : ClosedCoordinateDisk X, p ∈ interior K.carrier ∧
      ∃ (P : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
            (atlasVortexInitialOpen p) ℂ ∞)
          (hP : ∀ z : atlasVortexInitialOpen p, ‖P z‖ = 1),
        Nonempty (JJMath.Manifold.SmoothCirclePrimitive SurfaceRealModel
            (smoothUnitPhaseOneForm SurfaceRealModel P hP)) ∧
          ∀ (z : coordinateVortexPairOpen p q), (z : X) ∈ K.carrier →
            P ⟨(z : X), z.2.1⟩ = D.globalPhase z := by
  rcases exists_centered_closedCoordinateDisk_openDisk_subset_open_avoids_point
      (X := X) isOpen_univ (Set.mem_univ p) D.endpoints_ne.symm with
    ⟨K, hpInterior, _hRadius, _hchart, _hcenter,
      _hopenSubset, _hKSubset, hqK⟩
  let V : Set X := K.carrierᶜ
  have hV : IsExteriorComponent K.carrier V := by
    simpa [V] using closedCoordinateDisk_complement_isExteriorComponent K
  rcases hV.exists_circlePrimitive_extending_atlasVortex
      E K.compact (interior_subset hpInterior) (by simpa [V] using hqK) D with
    ⟨P, hP, hprimitive, hlocal⟩
  refine ⟨K, hpInterior, P, hP, hprimitive, ?_⟩
  intro z hzK
  exact hlocal z (by simpa [V] using hzK)

/-- A global punctured unit phase with a circle primitive, together with a
compact local vortex germ that certifies its winding at the puncture. -/
structure PuncturedAtlasVortexCirclePrimitiveData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    (p : X) where
  /-- The compensating endpoint of the local vortex. -/
  terminal : X
  /-- The compact atlas vortex furnishing the pole germ. -/
  vortex : AtlasVortexPairData X p terminal
  /-- A coordinate disk on which no later transport changes the vortex. -/
  localDisk : ClosedCoordinateDisk X
  /-- The puncture lies in the interior of the local disk. -/
  pole_mem_interior : p ∈ interior localDisk.carrier
  /-- The global smooth unit phase on the punctured surface. -/
  phase : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
    (atlasVortexInitialOpen p) ℂ ∞
  /-- The global phase has unit norm. -/
  norm_phase : ∀ z : atlasVortexInitialOpen p, ‖phase z‖ = 1
  /-- The logarithmic one-form of the phase has the phase as a circle
  primitive. -/
  primitive : Nonempty (JJMath.Manifold.SmoothCirclePrimitive SurfaceRealModel
    (smoothUnitPhaseOneForm SurfaceRealModel phase norm_phase))
  /-- On the local disk the global phase is exactly the original compact
  vortex phase. -/
  phase_eq_vortex : ∀ (z : coordinateVortexPairOpen p terminal),
    (z : X) ∈ localDisk.carrier →
      phase ⟨(z : X), z.2.1⟩ = vortex.globalPhase z

namespace PuncturedAtlasVortexCirclePrimitiveData

/-- Choose the canonical circle primitive carried in the data. -/
noncomputable def chosenPrimitive
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    JJMath.Manifold.SmoothCirclePrimitive SurfaceRealModel
      (smoothUnitPhaseOneForm SurfaceRealModel D.phase D.norm_phase) :=
  Classical.choice D.primitive

/-- The logarithmic form of the transported vortex phase, as a closed
one-form. -/
noncomputable def closedOneForm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    JJMath.Manifold.DeRhamClosedForms (I := SurfaceRealModel)
      (M := atlasVortexInitialOpen p) (A := ℝ) 1 :=
  D.chosenPrimitive.toClosedForm SurfaceRealModel

/-- Normalize the transported vortex form so that multiplying it by
`2 * pi` recovers the form represented by the unit phase. -/
noncomputable def normalizedClosedOneForm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    JJMath.Manifold.DeRhamClosedForms (I := SurfaceRealModel)
      (M := atlasVortexInitialOpen p) (A := ℝ) 1 :=
  (2 * Real.pi)⁻¹ • D.closedOneForm

/-- The normalized vortex class has the required `2 * pi` circle
primitive. -/
noncomputable def normalizedCirclePrimitive
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    JJMath.Manifold.SmoothCirclePrimitive SurfaceRealModel
      ((2 * Real.pi) • D.normalizedClosedOneForm.1) := by
  apply JJMath.Manifold.SmoothCirclePrimitive.congr SurfaceRealModel
    D.chosenPrimitive
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  change smoothUnitPhaseOneForm SurfaceRealModel D.phase D.norm_phase =
    (2 * Real.pi) • ((2 * Real.pi)⁻¹ •
      smoothUnitPhaseOneForm SurfaceRealModel D.phase D.norm_phase)
  rw [smul_smul, mul_inv_cancel₀ htwoPi, one_smul]

end PuncturedAtlasVortexCirclePrimitiveData

/-- Transport a prescribed atlas vortex to infinity and package the resulting
global puncture phase together with its unchanged local germ. -/
theorem AtlasVortexPairData.exists_puncturedCirclePrimitiveData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (D : AtlasVortexPairData X p q) :
    ∃ A : PuncturedAtlasVortexCirclePrimitiveData X p,
      A.vortex.chart = D.chart := by
  rcases D.exists_globalCirclePrimitive_preserving_local E with
    ⟨K, hpK, P, hP, hprimitive, hlocal⟩
  refine ⟨{
    terminal := q
    vortex := D
    localDisk := K
    pole_mem_interior := hpK
    phase := P
    norm_phase := hP
    primitive := hprimitive
    phase_eq_vortex := hlocal }, rfl⟩

/-- A prescribed compact atlas vortex has a transported global puncture
phase with a circle primitive. -/
theorem AtlasVortexPairData.puncturedCirclePrimitiveData_nonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (D : AtlasVortexPairData X p q) :
    Nonempty (PuncturedAtlasVortexCirclePrimitiveData X p) := by
  rcases D.exists_puncturedCirclePrimitiveData E with ⟨A, _⟩
  exact ⟨A⟩

/-- The transported puncture phase can be based in any prescribed atlas
chart containing the puncture. -/
theorem exists_puncturedAtlasVortexCirclePrimitiveData_from_chart
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    (E : SmoothRelativelyCompactExhaustion X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (p : X) (hp : p ∈ e.source) :
    ∃ A : PuncturedAtlasVortexCirclePrimitiveData X p,
      A.vortex.chart = e := by
  rcases exists_atlasVortexPairData_from_chart e he p hp with
    ⟨q, D, hDchart⟩
  rcases D.exists_puncturedCirclePrimitiveData E with ⟨A, hAchart⟩
  refine ⟨A, ?_⟩
  exact hAchart.trans hDchart

/-- Every puncture on a connected noncompact Riemann surface admits a global
unit phase with integral periods and a nontrivial compact vortex germ. -/
theorem puncturedAtlasVortexCirclePrimitiveData_nonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    (E : SmoothRelativelyCompactExhaustion X) (p : X) :
    Nonempty (PuncturedAtlasVortexCirclePrimitiveData X p) := by
  rcases exists_atlasVortexPairData_from p with ⟨q, ⟨D⟩⟩
  exact D.puncturedCirclePrimitiveData_nonempty E

end

end JJMath.Uniformization
