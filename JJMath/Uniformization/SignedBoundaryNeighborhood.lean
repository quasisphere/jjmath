import JJMath.Uniformization.SimplyConnectedExhaustion
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Signed neighborhoods of smooth frontier components

This file constructs a precompact neighborhood of a chosen connected frontier
component together with a continuous signed coordinate.  The coordinate is
negative on the domain side, positive on the exterior side, and zero exactly
on the chosen component.  The construction normalizes a partition-weighted
sum of local implicit-function coordinates, so the local sign convention is
preserved globally without first classifying the component as a circle.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The ambient carrier of the connected frontier component through a point. -/
def frontierComponentCarrier (U : Set X) (x₀ : frontier U) : Set X :=
  Subtype.val '' connectedComponent x₀

/--
%%handwave
name:
  A connected boundary component lies in the boundary
statement:
  For a subset \(U\) of a topological space and a point \(x_0\in\partial U\),
  the ambient image of the connected component of \(x_0\) in \(\partial U\)
  is contained in \(\partial U\).
proof:
  Every point of the component is, by construction, a point of the boundary
  subtype; forgetting the subtype therefore leaves it in \(\partial U\).
-/
theorem frontierComponentCarrier_subset_frontier
    (U : Set X) (x₀ : frontier U) :
    frontierComponentCarrier U x₀ ⊆ frontier U := by
  rintro x ⟨y, _hy, rfl⟩
  exact y.2

/--
%%handwave
name:
  Compactness of a connected boundary component
statement:
  If \(X\) is Hausdorff and \(\partial U\) is compact, then every connected
  component of \(\partial U\), viewed as a subset of \(X\), is compact.
proof:
  A connected component is closed in the compact space \(\partial U\), hence
  compact.  Its image under the continuous inclusion \(\partial U\hookrightarrow
  X\) is compact.
-/
theorem frontierComponentCarrier_isCompact
    [T2Space X] {U : Set X} (hfrontier : IsCompact (frontier U))
    (x₀ : frontier U) :
    IsCompact (frontierComponentCarrier U x₀) := by
  haveI : CompactSpace (frontier U) := isCompact_iff_compactSpace.mp hfrontier
  have hcomponent : IsCompact (connectedComponent x₀) :=
    isClosed_connectedComponent.isCompact
  exact hcomponent.image continuous_subtype_val

/--
%%handwave
name:
  Closedness of a connected boundary component
statement:
  If \(X\) is Hausdorff and \(\partial U\) is compact, then each connected
  component of \(\partial U\), regarded as a subset of \(X\), is closed.
proof:
  The component is compact by compactness of connected boundary components,
  and compact subsets of a Hausdorff space are closed.
-/
theorem frontierComponentCarrier_isClosed
    [T2Space X] {U : Set X} (hfrontier : IsCompact (frontier U))
    (x₀ : frontier U) :
    IsClosed (frontierComponentCarrier U x₀) :=
  (frontierComponentCarrier_isCompact hfrontier x₀).isClosed

/--
%%handwave
name:
  Ambient open isolation of a locally connected boundary component
statement:
  If \(X\) is Hausdorff and \(\partial U\) is locally connected, then for each
  \(x_0\in\partial U\) there is an open set \(O\subseteq X\) such that the
  connected component of \(x_0\) in \(\partial U\), viewed in \(X\), is
  exactly \(O\cap\partial U\).
proof:
  Connected components of a locally connected space are open.  Express this
  open subset of the subspace \(\partial U\) as the inverse image of an
  ambient open set and then pass through the subtype inclusion.
-/
theorem exists_open_frontierComponentCarrier_isolation
    [T2Space X] (U : Set X) [LocallyConnectedSpace (frontier U)]
    (x₀ : frontier U) :
    ∃ O : Set X, IsOpen O ∧
      frontierComponentCarrier U x₀ = O ∩ frontier U := by
  have hopen : IsOpen (connectedComponent x₀) := isOpen_connectedComponent
  rcases isOpen_induced_iff.mp hopen with ⟨O, hOopen, hOeq⟩
  refine ⟨O, hOopen, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyO : (y : X) ∈ O := by
      have : y ∈ Subtype.val ⁻¹' O :=
        (Set.ext_iff.mp hOeq y).mpr hy
      exact this
    exact ⟨hyO, y.2⟩
  · rintro ⟨hxO, hxfrontier⟩
    let y : frontier U := ⟨x, hxfrontier⟩
    have hy : y ∈ connectedComponent x₀ := by
      exact (Set.ext_iff.mp hOeq y).mp hxO
    exact ⟨y, hy, rfl⟩

/-- A local continuous defining function carrying the common convention that
the domain side has negative sign. -/
structure SignedDefiningChart [ChartedSpace ℂ X]
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) where
  neighborhood : Set X
  neighborhood_isOpen : IsOpen neighborhood
  point_mem : (p : X) ∈ neighborhood
  definingFunction : X → ℝ
  definingFunction_continuous : ContinuousOn definingFunction neighborhood
  domain_iff_neg : ∀ x ∈ neighborhood,
    x ∈ D.carrier ↔ definingFunction x < 0
  frontier_iff_zero : ∀ x ∈ neighborhood,
    x ∈ frontier D.carrier ↔ definingFunction x = 0

/--
%%handwave
name:
  Signed local defining function inside a prescribed neighborhood
statement:
  Let \(D\) be a smooth-boundary domain, let \(p\in\partial D\), and let
  \(A\) be an open neighborhood of \(p\).  There is an open neighborhood
  \(W\subseteq A\) of \(p\) and a continuous real function \(r\) on \(W\)
  such that, for \(x\in W\),
  \[
    x\in D\iff r(x)<0,
    \qquad x\in\partial D\iff r(x)=0.
  \]
proof:
  Take the regular local defining function supplied by smoothness of the
  boundary and straighten its zero set by the implicit-function theorem.
  Intersect its valid neighborhood with \(A\), and pull the defining function
  back through the surface coordinate.  The local sign and zero-set
  equivalences persist on this smaller open neighborhood.
-/
theorem exists_signedDefiningChart_within
    [ChartedSpace ℂ X]
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier)
    {A : Set X} (hAopen : IsOpen A) (hpA : (p : X) ∈ A) :
    ∃ data : SignedDefiningChart D p, data.neighborhood ⊆ A := by
  rcases D.smooth_boundary p p.2 with
    ⟨e, he, hpe, r, hrsmooth, dr, hrderiv, hdrnz, hlocal⟩
  have hprops_p := hlocal.self_of_nhds
  have hrzero : r (e (p : X)) = 0 := hprops_p.2.2.mp p.2
  rcases smoothPlaneRegularZeroSet_implicitCoord_fst_eq
      hrsmooth.contDiffAt hrderiv hdrnz hrzero with
    ⟨Phi, hpPhi, hPhi_fst, _hPhi_zero⟩
  have hr_continuous : ContinuousOn r Phi.source := by
    exact Phi.continuousOn.fst.congr (fun z hz => (hPhi_fst z hz).symm)
  let N : Set X :=
    A ∩ (e.source ∩ e ⁻¹' Phi.source) ∩
      {x | x ∈ e.source ∧
        (x ∈ D.carrier ↔ r (e x) < 0) ∧
          (x ∈ frontier D.carrier ↔ r (e x) = 0)}
  have hlast_nhds :
      {x | x ∈ e.source ∧
        (x ∈ D.carrier ↔ r (e x) < 0) ∧
          (x ∈ frontier D.carrier ↔ r (e x) = 0)} ∈ 𝓝 (p : X) :=
    hlocal
  have hN_nhds : N ∈ 𝓝 (p : X) := by
    exact Filter.inter_mem
      (Filter.inter_mem
        (hAopen.mem_nhds hpA)
        ((e.isOpen_inter_preimage Phi.open_source).mem_nhds ⟨hpe, hpPhi⟩))
      hlast_nhds
  rcases mem_nhds_iff.mp hN_nhds with ⟨W, hWN, hWopen, hpW⟩
  let f : X → ℝ := fun x => r (e x)
  have hf_continuous : ContinuousOn f W := by
    exact hr_continuous.comp
      (e.continuousOn.mono (fun x hxW => (hWN hxW).1.2.1))
      (fun x hxW => (hWN hxW).1.2.2)
  refine ⟨{
    neighborhood := W
    neighborhood_isOpen := hWopen
    point_mem := hpW
    definingFunction := f
    definingFunction_continuous := hf_continuous
    domain_iff_neg := ?_
    frontier_iff_zero := ?_ }, ?_⟩
  · intro x hxW
    exact (hWN hxW).2.2.1
  · intro x hxW
    exact (hWN hxW).2.2.2
  · intro x hxW
    exact (hWN hxW).1.1

/-- A precompact neighborhood of one frontier component, equipped with a
continuous function that records its two sides by sign. -/
structure SignedFrontierComponentNeighborhood [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) where
  neighborhood : Set X
  neighborhood_isOpen : IsOpen neighborhood
  neighborhood_compactClosure : IsCompact (closure neighborhood)
  component_subset : frontierComponentCarrier D.carrier p ⊆ neighborhood
  frontier_inter :
    neighborhood ∩ frontier D.carrier = frontierComponentCarrier D.carrier p
  coordinate : X → ℝ
  coordinate_continuous : ContinuousOn coordinate neighborhood
  domain_iff_neg : ∀ x ∈ neighborhood,
    x ∈ D.carrier ↔ coordinate x < 0
  frontier_iff_zero : ∀ x ∈ neighborhood,
    x ∈ frontier D.carrier ↔ coordinate x = 0

/--
%%handwave
name:
  Signed neighborhood of a smooth boundary component
statement:
  Every connected component of the boundary of a smooth relatively compact
  domain has a precompact open neighborhood carrying a continuous real-valued
  function which is negative precisely on the domain side and vanishes
  precisely on that boundary component.
proof:
  The local defining functions all use the convention that the domain is the
  negative side.  Isolate the chosen compact component from the other boundary
  components, choose a smooth partition of unity subordinate to implicit-function
  neighborhoods, and divide the weighted sum of the defining functions by the
  total partition weight.  Positivity of the weights preserves the sign, while
  the normalization prevents the coordinate from collapsing at the edge of the
  cover.
-/
theorem exists_signedFrontierComponentNeighborhood
    [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    Nonempty (SignedFrontierComponentNeighborhood D p) := by
  classical
  letI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  letI : LocallyConnectedSpace (frontier D.carrier) :=
    smoothBoundaryDomain_frontier_locallyConnected D
  let C : Set X := frontierComponentCarrier D.carrier p
  have hCcompact : IsCompact C := by
    exact frontierComponentCarrier_isCompact
      (smoothBoundaryDomain_frontier_compact D) p
  have hCclosed : IsClosed C := hCcompact.isClosed
  rcases exists_open_frontierComponentCarrier_isolation D.carrier p with
    ⟨O, hOopen, hCO⟩
  rcases exists_isOpen_superset_and_isCompact_closure hCcompact with
    ⟨P, hPopen, hCP, hPcompact⟩
  have hCOsub : C ⊆ O := by
    intro x hxC
    change x ∈ frontierComponentCarrier D.carrier p at hxC
    rw [hCO] at hxC
    exact hxC.1
  let A : Set X := O ∩ P
  have hAopen : IsOpen A := hOopen.inter hPopen
  have hCA : C ⊆ A := fun x hx => ⟨hCOsub hx, hCP hx⟩
  let pointOf (q : C) : frontier D.carrier :=
    ⟨(q : X), frontierComponentCarrier_subset_frontier D.carrier p q.2⟩
  have localExists (q : C) :
      ∃ data : SignedDefiningChart D (pointOf q), data.neighborhood ⊆ A :=
    exists_signedDefiningChart_within D (pointOf q) hAopen (hCA q.2)
  let chartData (q : C) : SignedDefiningChart D (pointOf q) :=
    Classical.choose (localExists q)
  have hlocal_sub (q : C) : (chartData q).neighborhood ⊆ A :=
    Classical.choose_spec (localExists q)
  let W (q : C) : Set X := (chartData q).neighborhood
  have hWopen (q : C) : IsOpen (W q) := (chartData q).neighborhood_isOpen
  have hCW : C ⊆ ⋃ q : C, W q := by
    intro x hxC
    let q : C := ⟨x, hxC⟩
    exact mem_iUnion.mpr ⟨q, (chartData q).point_mem⟩
  haveI : SigmaCompactSpace X := by infer_instance
  rcases SmoothPartitionOfUnity.exists_isSubordinate
      SurfaceRealModel hCclosed W hWopen hCW with
    ⟨rho, hrhoW⟩
  let weight : X → ℝ := fun x => ∑ᶠ q : C, rho q x
  let numerator : X → ℝ := fun x =>
    ∑ᶠ q : C, rho q x • (chartData q).definingFunction x
  have hweight_smooth :
      ContMDiff SurfaceRealModel 𝓘(ℝ, ℝ) ∞ weight := by
    exact rho.contMDiff_sum
  have hnumerator_continuous : Continuous numerator := by
    exact PartitionOfUnity.IsSubordinate.continuous_finsum_smul
      hWopen hrhoW.toPartitionOfUnity
      (fun q => (chartData q).definingFunction_continuous)
  let N : Set X := {x | (1 / 2 : ℝ) < weight x}
  have hNopen : IsOpen N := by
    exact isOpen_lt continuous_const hweight_smooth.continuous
  have hweight_one_on_C : ∀ x ∈ C, weight x = 1 := by
    intro x hxC
    exact rho.sum_eq_one hxC
  have hCN : C ⊆ N := by
    intro x hxC
    change (1 / 2 : ℝ) < weight x
    rw [hweight_one_on_C x hxC]
    norm_num
  have active_mem_W {x : X} {q : C} (hq : rho q x ≠ 0) : x ∈ W q := by
    apply hrhoW q
    exact subset_tsupport _ hq
  have hNP : N ⊆ P := by
    intro x hxN
    have hweight_ne : weight x ≠ 0 := ne_of_gt (lt_trans (by norm_num) hxN)
    have hexists : ∃ q : C, rho q x ≠ 0 := by
      by_contra! hall
      apply hweight_ne
      simp [weight, hall]
    rcases hexists with ⟨q, hq⟩
    exact (hlocal_sub q (active_mem_W hq)).2
  have hNcompact : IsCompact (closure N) :=
    hPcompact.closure_of_subset (hNP.trans subset_closure)
  have hNfrontier : N ∩ frontier D.carrier = C := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxN, hxfrontier⟩
      have hweight_ne : weight x ≠ 0 := ne_of_gt (lt_trans (by norm_num) hxN)
      have hexists : ∃ q : C, rho q x ≠ 0 := by
        by_contra! hall
        apply hweight_ne
        simp [weight, hall]
      rcases hexists with ⟨q, hq⟩
      have hxO : x ∈ O := (hlocal_sub q (active_mem_W hq)).1
      change x ∈ frontierComponentCarrier D.carrier p
      rw [hCO]
      exact ⟨hxO, hxfrontier⟩
    · intro x hxC
      exact ⟨hCN hxC, frontierComponentCarrier_subset_frontier D.carrier p hxC⟩
  let y : X → ℝ := fun x => numerator x / weight x
  have hy_continuous : ContinuousOn y N :=
    hnumerator_continuous.continuousOn.div hweight_smooth.continuous.continuousOn
      (fun x hxN => ne_of_gt (lt_trans (by norm_num) hxN))
  have active_mem_local {x : X} {q : C} (hq : q ∈ rho.finsupport x) :
      x ∈ (chartData q).neighborhood := by
    apply active_mem_W
    exact (rho.mem_finsupport x).mp hq
  have hfinsupport_nonempty {x : X} (hxN : x ∈ N) :
      (rho.finsupport x).Nonempty := by
    by_contra hempty
    have hall : ∀ q : C, rho q x = 0 := by
      intro q
      by_contra hq
      have : q ∈ rho.finsupport x := (rho.mem_finsupport x).mpr hq
      exact hempty ⟨q, this⟩
    have hzero : weight x = 0 := by simp [weight, hall]
    change (1 / 2 : ℝ) < weight x at hxN
    linarith
  have hweight_pos {x : X} (hxN : x ∈ N) : 0 < weight x :=
    lt_trans (by norm_num) hxN
  have hnumerator_neg {x : X} (hxN : x ∈ N) (hxD : x ∈ D.carrier) :
      numerator x < 0 := by
    change (∑ᶠ q : C, rho q x • (chartData q).definingFunction x) < 0
    rw [← rho.sum_finsupport_smul_eq_finsum x
      (fun q x => (chartData q).definingFunction x)]
    apply Finset.sum_neg
    · intro q hq
      have hrho_pos : 0 < rho q x :=
        lt_of_le_of_ne (rho.nonneg q x) (Ne.symm ((rho.mem_finsupport x).mp hq))
      have hlocal_neg : (chartData q).definingFunction x < 0 :=
        ((chartData q).domain_iff_neg x (active_mem_local hq)).mp hxD
      simpa [smul_eq_mul] using mul_neg_of_pos_of_neg hrho_pos hlocal_neg
    · exact hfinsupport_nonempty hxN
  have hnumerator_zero {x : X} (hxN : x ∈ N)
      (hxfrontier : x ∈ frontier D.carrier) : numerator x = 0 := by
    change (∑ᶠ q : C, rho q x • (chartData q).definingFunction x) = 0
    rw [← rho.sum_finsupport_smul_eq_finsum x
      (fun q x => (chartData q).definingFunction x)]
    apply Finset.sum_eq_zero
    intro q hq
    have hlocal_zero : (chartData q).definingFunction x = 0 :=
      ((chartData q).frontier_iff_zero x (active_mem_local hq)).mp hxfrontier
    simp [hlocal_zero]
  have hnumerator_pos {x : X} (hxN : x ∈ N)
      (hxD : x ∉ D.carrier) (hxfrontier : x ∉ frontier D.carrier) :
      0 < numerator x := by
    change 0 < (∑ᶠ q : C, rho q x • (chartData q).definingFunction x)
    rw [← rho.sum_finsupport_smul_eq_finsum x
      (fun q x => (chartData q).definingFunction x)]
    apply Finset.sum_pos
    · intro q hq
      have hrho_pos : 0 < rho q x :=
        lt_of_le_of_ne (rho.nonneg q x) (Ne.symm ((rho.mem_finsupport x).mp hq))
      have hlocal_nonneg : 0 ≤ (chartData q).definingFunction x :=
        le_of_not_gt (fun hneg => hxD
          (((chartData q).domain_iff_neg x (active_mem_local hq)).mpr hneg))
      have hlocal_ne : (chartData q).definingFunction x ≠ 0 :=
        fun hzero => hxfrontier
          (((chartData q).frontier_iff_zero x (active_mem_local hq)).mpr hzero)
      have hlocal_pos : 0 < (chartData q).definingFunction x :=
        lt_of_le_of_ne hlocal_nonneg (Ne.symm hlocal_ne)
      simpa [smul_eq_mul] using mul_pos hrho_pos hlocal_pos
    · exact hfinsupport_nonempty hxN
  refine ⟨{
    neighborhood := N
    neighborhood_isOpen := hNopen
    neighborhood_compactClosure := hNcompact
    component_subset := hCN
    frontier_inter := hNfrontier
    coordinate := y
    coordinate_continuous := hy_continuous
    domain_iff_neg := ?_
    frontier_iff_zero := ?_ }⟩
  · intro x hxN
    constructor
    · intro hxD
      exact div_neg_of_neg_of_pos (hnumerator_neg hxN hxD) (hweight_pos hxN)
    · intro hyneg
      by_contra hxD
      by_cases hxfrontier : x ∈ frontier D.carrier
      · have hnumzero := hnumerator_zero hxN hxfrontier
        simp [y, hnumzero] at hyneg
      · have hnumpos := hnumerator_pos hxN hxD hxfrontier
        exact (not_lt_of_ge (div_nonneg hnumpos.le (hweight_pos hxN).le)) hyneg
  · intro x hxN
    constructor
    · intro hxfrontier
      simp [y, hnumerator_zero hxN hxfrontier]
    · intro hyzero
      by_contra hxfrontier
      by_cases hxD : x ∈ D.carrier
      · have hnumneg := hnumerator_neg hxN hxD
        have : y x < 0 := div_neg_of_neg_of_pos hnumneg (hweight_pos hxN)
        linarith
      · have hnumpos := hnumerator_pos hxN hxD hxfrontier
        have : 0 < y x := div_pos hnumpos (hweight_pos hxN)
        linarith

/--
%%handwave
name:
  Smooth step across a signed boundary neighborhood
statement:
  On any open subset of a signed boundary neighborhood and for every positive
  number \(\varepsilon\), there is a smooth function which is zero where the
  signed coordinate is at most \(-\varepsilon\) and one where it is at least
  \(\varepsilon\).
proof:
  The negative and positive closed strips are disjoint.  Apply smooth Urysohn
  separation on the open submanifold.
-/
theorem SignedFrontierComponentNeighborhood.exists_smoothStep_on_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (S : SignedFrontierComponentNeighborhood D p)
    (U : TopologicalSpace.Opens X)
    (hUN : (U : Set X) ⊆ S.neighborhood)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : C^∞⟮SurfaceRealModel, U; ℝ⟯,
      (∀ x : U, S.coordinate x ≤ -ε → f x = 0) ∧
        (∀ x : U, ε ≤ S.coordinate x → f x = 1) := by
  letI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  haveI : LocallyCompactSpace U := by
    exact U.isOpen.locallyCompactSpace
  haveI : SigmaCompactSpace U := by infer_instance
  let y : U → ℝ := fun x => S.coordinate x
  have hy : Continuous y := by
    exact S.coordinate_continuous.comp_continuous continuous_subtype_val
      (fun x => hUN x.2)
  let A : Set U := {x | y x ≤ -ε}
  let B : Set U := {x | ε ≤ y x}
  have hAclosed : IsClosed A := isClosed_le hy continuous_const
  have hBclosed : IsClosed B := isClosed_le continuous_const hy
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    change y x ≤ -ε at hxA
    change ε ≤ y x at hxB
    linarith
  rcases exists_contMDiffMap_zero_one_of_isClosed
      SurfaceRealModel hAclosed hBclosed hAB with
    ⟨f, hfA, hfB, _hf_range⟩
  refine ⟨f, ?_, ?_⟩
  · intro x hx
    exact hfA hx
  · intro x hx
    exact hfB hx

/--
%%handwave
name:
  A signed boundary component has a transition band
statement:
  On a noncompact connected surface, a signed neighborhood of a compact
  boundary component contains a smaller precompact open band and a positive
  number \(\varepsilon\) such that the absolute value of the signed coordinate
  is at least \(2\varepsilon\) on the frontier of the band.
proof:
  Shrink the neighborhood around the compact component.  Its new frontier is
  compact and nonempty.  The signed coordinate has no zero there, since all of
  its zeros lie on the chosen component in the interior.  Its absolute value
  therefore has a positive minimum on the new frontier.
-/
theorem SignedFrontierComponentNeighborhood.exists_band_gap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (S : SignedFrontierComponentNeighborhood D p)
    (hnoncompact : ¬ CompactSpace X) :
    ∃ V : Set X, IsOpen V ∧
      frontierComponentCarrier D.carrier p ⊆ V ∧
        closure V ⊆ S.neighborhood ∧ IsCompact (closure V) ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x ∈ frontier V, 2 * ε ≤ |S.coordinate x| := by
  let C : Set X := frontierComponentCarrier D.carrier p
  have hCcompact : IsCompact C :=
    frontierComponentCarrier_isCompact
      (smoothBoundaryDomain_frontier_compact D) p
  have hN_nhds : S.neighborhood ∈ 𝓝ˢ C :=
    S.neighborhood_isOpen.mem_nhdsSet.mpr S.component_subset
  rcases hCcompact.exists_isOpen_closure_subset hN_nhds with
    ⟨V, hVopen, hCV, hVclosure⟩
  have hVcompact : IsCompact (closure V) :=
    S.neighborhood_compactClosure.of_isClosed_subset isClosed_closure
      (hVclosure.trans subset_closure)
  have hfrontier_compact : IsCompact (frontier V) := by
    rw [frontier, hVopen.interior_eq]
    exact hVcompact.diff hVopen
  have hCnonempty : C.Nonempty := by
    refine ⟨(p : X), ?_⟩
    exact ⟨p, mem_connectedComponent, rfl⟩
  have hVnonempty : V.Nonempty := hCnonempty.mono hCV
  have hfrontier_nonempty : (frontier V).Nonempty := by
    by_contra hempty
    have hclopen : IsClopen V :=
      isClopen_iff_frontier_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hempty)
    have hVuniv : V = (univ : Set X) := hclopen.eq_univ hVnonempty
    apply hnoncompact
    apply isCompact_univ_iff.mp
    simpa [hVuniv] using hVcompact
  have hfrontier_subset_N : frontier V ⊆ S.neighborhood :=
    frontier_subset_closure.trans hVclosure
  have habs_continuous :
      ContinuousOn (fun x => |S.coordinate x|) (frontier V) := by
    exact (S.coordinate_continuous.mono hfrontier_subset_N).abs
  rcases hfrontier_compact.exists_isMinOn hfrontier_nonempty habs_continuous with
    ⟨z, hzfrontier, hzmin⟩
  have hzN : z ∈ S.neighborhood := hfrontier_subset_N hzfrontier
  have hzcoord_ne : S.coordinate z ≠ 0 := by
    intro hzzero
    have hzDfrontier : z ∈ frontier D.carrier :=
      (S.frontier_iff_zero z hzN).mpr hzzero
    have hzC : z ∈ frontierComponentCarrier D.carrier p := by
      rw [← S.frontier_inter]
      exact ⟨hzN, hzDfrontier⟩
    have hzV : z ∈ V := hCV hzC
    have hznotV : z ∉ V := by
      have := hzfrontier.2
      simpa [hVopen.interior_eq] using this
    exact hznotV hzV
  have habsz_pos : 0 < |S.coordinate z| := abs_pos.mpr hzcoord_ne
  let ε : ℝ := |S.coordinate z| / 4
  refine ⟨V, hVopen, hCV, hVclosure, hVcompact, ε, by
    dsimp [ε]
    positivity, ?_⟩
  intro x hxfrontier
  have hmin := isMinOn_iff.mp hzmin x hxfrontier
  dsimp [ε]
  linarith

end
end Uniformization
end JJMath
