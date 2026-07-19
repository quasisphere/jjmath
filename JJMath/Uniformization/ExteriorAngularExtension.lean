import JJMath.Manifold.AnnularCohomologyMayerVietoris
import JJMath.Uniformization.ExteriorMassConsolidation
import JJMath.Uniformization.SmoothFrontierMayerVietoris

/-!
# Extending an angular class across an exterior component

An angular class on a full annular collar is cut off only on the exterior
side.  Its exterior derivative is then a compactly supported two-form in the
adjacent exterior component.  Mass transport to infinity supplies a primitive
of that defect, leaving a closed one-form whose restriction to the domain
half-collar is the original nonzero angular class.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

/-! ## Reassociating nested open submanifolds -/

/-- An ambient open set, regarded as an open set inside a larger ambient
open set. -/
def openWithinOpen
    (R A : TopologicalSpace.Opens X) : TopologicalSpace.Opens R :=
  ⟨{x : R | (x : X) ∈ A},
    A.isOpen.preimage continuous_subtype_val⟩

/-- Reassociating two nested open-submanifold subtypes is a diffeomorphism. -/
noncomputable def openWithinOpenDiffeomorph
    (R A : TopologicalSpace.Opens X) (hAR : A ≤ R) :
    openWithinOpen R A ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ A := by
  let toRaw : openWithinOpen R A → X := fun x => (x.1 : X)
  have htoRaw : ContMDiff SurfaceRealModel SurfaceRealModel ∞ toRaw := by
    exact (contMDiff_subtype_val (I := SurfaceRealModel) (n := ∞)
      (U := R)).comp
        (contMDiff_subtype_val (I := SurfaceRealModel) (n := ∞)
          (U := openWithinOpen R A))
  let toA : openWithinOpen R A → A := fun x => ⟨toRaw x, x.2⟩
  have htoA : ContMDiff SurfaceRealModel SurfaceRealModel ∞ toA :=
    ContMDiff.codRestrict_open htoRaw A (fun x => x.2)
  let fromR : A → R := TopologicalSpace.Opens.inclusion hAR
  have hfromR : ContMDiff SurfaceRealModel SurfaceRealModel ∞ fromR :=
    contMDiff_inclusion hAR
  let fromA : A → openWithinOpen R A := fun x => ⟨fromR x, x.2⟩
  have hfromA : ContMDiff SurfaceRealModel SurfaceRealModel ∞ fromA :=
    ContMDiff.codRestrict_open hfromR (openWithinOpen R A) (fun x => x.2)
  let e : openWithinOpen R A ≃ A :=
    { toFun := toA
      invFun := fromA
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  exact
    { toEquiv := e
      contMDiff_toFun := htoA
      contMDiff_invFun := hfromA }

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  One nested annular removal preserves vanishing first cohomology
statement:
  Let \(L,N\subseteq R\) be open subsets covering \(R\), with
  \(L\cap N\cong S^1\times\mathbb R\).  If
  \(H^1_{\mathrm{dR}}(R;\mathbb R)=0\) and
  \(H^1_{\mathrm{dR}}(L;\mathbb R)\ne0\), then
  \(H^1_{\mathrm{dR}}(N;\mathbb R)=0\).
proof:
  Regard \(L\) and \(N\) as open submanifolds of \(R\) and apply the
  annular Mayer--Vietoris reduction.  Canonical diffeomorphisms identify
  their cohomology with that of the original open subsets of the ambient
  surface.
-/
theorem subsingleton_deRhamH1_of_nested_annular_removal
    (R L N : TopologicalSpace.Opens X)
    (hLR : L ≤ R) (hNR : N ≤ R)
    (hcover : openWithinOpen R L ⊔ openWithinOpen R N = ⊤)
    (phi : ((openWithinOpen R L ⊓ openWithinOpen R N :
      TopologicalSpace.Opens R)) ≃ₘ⟮SurfaceRealModel,
        AnnularCylinderModel⟯ Circle × ℝ)
    (v : Circle)
    (hR : Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := R) (A := ℝ) 1))
    (hL : ¬ Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := L) (A := ℝ) 1)) :
    Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := N) (A := ℝ) 1) := by
  letI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  letI : LocallyCompactSpace R := R.isOpen.locallyCompactSpace
  letI : SigmaCompactSpace R := by infer_instance
  letI : Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := R) (A := ℝ) 1) := hR
  have hleft : ¬ Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := openWithinOpen R L) (A := ℝ) 1) := by
    intro hwithin
    apply hL
    exact deRhamCohomology_subsingleton_of_diffeomorphic
      SurfaceRealModel SurfaceRealModel
        (openWithinOpenDiffeomorph R L hLR).symm 1 hwithin
  have hnextWithin : Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := openWithinOpen R N) (A := ℝ) 1) :=
    deRhamH1_subsingleton_of_mayerVietoris_annular_and_left_nontrivial
      SurfaceRealModel (openWithinOpen R L) (openWithinOpen R N)
        hcover phi v hleft
  exact deRhamCohomology_subsingleton_of_diffeomorphic
    SurfaceRealModel SurfaceRealModel
      (openWithinOpenDiffeomorph R N hNR).symm 1 hnextWithin

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  Vanishing first cohomology along a sequence of annular removals
statement:
  Let \(R_0\supseteq R_1\supseteq\cdots\) be open sets such that each
  \(R_n\) is covered by \(L_n\) and \(R_{n+1}\), their overlap is an annular
  cylinder, and \(H^1_{\mathrm{dR}}(L_n;\mathbb R)\ne0\).  If
  \(H^1_{\mathrm{dR}}(R_0;\mathbb R)=0\), then
  \(H^1_{\mathrm{dR}}(R_n;\mathbb R)=0\) for every \(n\).
proof:
  Induct on \(n\), applying the one-step annular Mayer--Vietoris removal at
  each successor.
-/
theorem subsingleton_deRhamH1_of_finite_nested_annular_removals
    (R L : ℕ → TopologicalSpace.Opens X)
    (hnext : ∀ n : ℕ, R (n + 1) ≤ R n)
    (hleftSubset : ∀ n : ℕ, L n ≤ R n)
    (hcover : ∀ n : ℕ,
      openWithinOpen (R n) (L n) ⊔
        openWithinOpen (R n) (R (n + 1)) = ⊤)
    (phi : ∀ n : ℕ,
      ((openWithinOpen (R n) (L n) ⊓
        openWithinOpen (R n) (R (n + 1)) :
          TopologicalSpace.Opens (R n))) ≃ₘ⟮SurfaceRealModel,
            AnnularCylinderModel⟯ Circle × ℝ)
    (v : ℕ → Circle)
    (hleft : ∀ n : ℕ, ¬ Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := L n) (A := ℝ) 1))
    (hzero : Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := R 0) (A := ℝ) 1)) :
    ∀ n : ℕ, Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := R n) (A := ℝ) 1) := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      exact subsingleton_deRhamH1_of_nested_annular_removal
        (R n) (L n) (R (n + 1))
          (hleftSubset n) (hnext n) (hcover n) (phi n) (v n)
          ih (hleft n)

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  Vanishing of \(H^1\) through finitely many annular removals
statement:
  Let
  \(R_0\supseteq R_1\supseteq\cdots\supseteq R_m\) be open sets.  Suppose
  each \(R_n\) is covered by open subsets \(L_n\) and \(R_{n+1}\), their
  overlap is diffeomorphic to \(S^1\times\mathbb R\), and
  \(H^1_{\mathrm{dR}}(L_n)\neq0\).  If
  \(H^1_{\mathrm{dR}}(R_0)=0\), then
  \[
    H^1_{\mathrm{dR}}(R_m)=0.
  \]
proof:
  Induct on \(n\).  At each step, the annular Mayer--Vietoris reduction sends
  vanishing of \(H^1_{\mathrm{dR}}(R_n)\), together with nonvanishing on
  \(L_n\), to vanishing on \(R_{n+1}\).
-/
theorem subsingleton_deRhamH1_of_bounded_nested_annular_removals
    (m : ℕ) (R L : ℕ → TopologicalSpace.Opens X)
    (hnext : ∀ n : ℕ, n < m → R (n + 1) ≤ R n)
    (hleftSubset : ∀ n : ℕ, n < m → L n ≤ R n)
    (hcover : ∀ n : ℕ, n < m →
      openWithinOpen (R n) (L n) ⊔
        openWithinOpen (R n) (R (n + 1)) = ⊤)
    (phi : ∀ (n : ℕ) (_hn : n < m),
      ((openWithinOpen (R n) (L n) ⊓
        openWithinOpen (R n) (R (n + 1)) :
          TopologicalSpace.Opens (R n))) ≃ₘ⟮SurfaceRealModel,
            AnnularCylinderModel⟯ Circle × ℝ)
    (v : ℕ → Circle)
    (hleft : ∀ n : ℕ, n < m → ¬ Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := L n) (A := ℝ) 1))
    (hzero : Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := R 0) (A := ℝ) 1)) :
    Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := R m) (A := ℝ) 1) := by
  have haux : ∀ n : ℕ, n ≤ m → Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := R n) (A := ℝ) 1) := by
    intro n hn
    induction n with
    | zero => exact hzero
    | succ n ih =>
        have hnm : n < m := Nat.lt_of_succ_le hn
        exact subsingleton_deRhamH1_of_nested_annular_removal
          (R n) (L n) (R (n + 1))
            (hleftSubset n hnm) (hnext n hnm) (hcover n hnm)
            (phi n hnm) (v n) (ih (Nat.le_of_lt hnm)) (hleft n hnm)
  exact haux m le_rfl

/--
%%handwave
name:
  Complementary components with meeting closures coincide
statement:
  Let \(D\) be a smooth boundary domain.  If two connected components
  \(V,Z\) of \(X\setminus\overline D\) have
  \(\overline V\cap\overline Z\ne\varnothing\), then \(V=Z\).
proof:
  If a meeting point lies in either open component, the components intersect
  and hence coincide.  Otherwise it lies on both frontiers and therefore on
  the smooth boundary of \(D\).  Local uniqueness of the complementary
  component incident to a boundary interval then again identifies \(V\) and
  \(Z\).
-/
theorem smoothBoundaryDomain_complement_components_eq_of_closures_meet
    (D : SmoothBoundaryDomain X)
    (V Z : Set X)
    (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (hZ : IsComponentOf Z (closure D.carrier)ᶜ)
    (hmeet : (closure V ∩ closure Z).Nonempty) :
    V = Z := by
  rcases hmeet with ⟨x, hxVcl, hxZcl⟩
  let hVopen : IsOpen V :=
    hV.isOpen_of_isOpen isClosed_closure.isOpen_compl
  let hZopen : IsOpen Z :=
    hZ.isOpen_of_isOpen isClosed_closure.isOpen_compl
  by_cases hxV : x ∈ V
  · rcases (mem_closure_iff.mp hxZcl) V hVopen hxV with
      ⟨y, hyZ, hyV⟩
    exact hV.eq_of_inter_nonempty hZ ⟨y, hyZ, hyV⟩
  by_cases hxZ : x ∈ Z
  · rcases (mem_closure_iff.mp hxVcl) Z hZopen hxZ with
      ⟨y, hyV, hyZ⟩
    exact hV.eq_of_inter_nonempty hZ ⟨y, hyZ, hyV⟩
  have hxVfront : x ∈ frontier V := by
    rw [frontier, hVopen.interior_eq]
    exact ⟨hxVcl, hxV⟩
  have hxZfront : x ∈ frontier Z := by
    rw [frontier, hZopen.interior_eq]
    exact ⟨hxZcl, hxZ⟩
  have hxD : x ∈ frontier D.carrier :=
    hV.frontier_subset_smoothBoundaryDomain_frontier D V hxVfront
  let p : frontier D.carrier := ⟨x, hxD⟩
  rcases
      smoothBoundaryDomain_boundary_interval_unique_incident_closure_complement_component
        D p with
    ⟨t, ht, V0, _hfrontier, hunique⟩
  have hpt : p ∈ t := mem_of_mem_nhds ht
  have hVmem :
      (⟨V, hV⟩ : {A : Set X //
        IsComponentOf A (closure D.carrier)ᶜ}) ∈
        {A : {A : Set X //
            IsComponentOf A (closure D.carrier)ᶜ} |
          (({q : frontier D.carrier |
              (q : X) ∈ frontier (A : Set X)} ∩ t).Nonempty)} :=
    ⟨p, hxVfront, hpt⟩
  have hZmem :
      (⟨Z, hZ⟩ : {A : Set X //
        IsComponentOf A (closure D.carrier)ᶜ}) ∈
        {A : {A : Set X //
            IsComponentOf A (closure D.carrier)ᶜ} |
          (({q : frontier D.carrier |
              (q : X) ∈ frontier (A : Set X)} ∩ t).Nonempty)} :=
    ⟨p, hxZfront, hpt⟩
  have hVV0 : (⟨V, hV⟩ : {A : Set X //
      IsComponentOf A (closure D.carrier)ᶜ}) = V0 :=
    Set.mem_singleton_iff.mp (hunique hVmem)
  have hZV0 : (⟨Z, hZ⟩ : {A : Set X //
      IsComponentOf A (closure D.carrier)ᶜ}) = V0 :=
    Set.mem_singleton_iff.mp (hunique hZmem)
  exact congrArg Subtype.val (hVV0.trans hZV0.symm)

/--
%%handwave
name:
  A smooth domain misses the closure of every complementary component
statement:
  If \(Z\) is a connected component of
  \(X\setminus\overline D\), then
  \(D\cap\overline Z=\varnothing\).
proof:
  If a point of the open set \(D\) lay in \(\overline Z\), every
  neighborhood of it, in particular \(D\), would meet \(Z\).  Such a point
  would belong both to \(D\) and to the complement of \(\overline D\), a
  contradiction.
-/
theorem smoothBoundaryDomain_carrier_disjoint_complement_component_closure
    (D : SmoothBoundaryDomain X)
    (Z : Set X) (hZ : IsComponentOf Z (closure D.carrier)ᶜ) :
    Disjoint D.carrier (closure Z) := by
  rw [Set.disjoint_left]
  intro x hxD hxZcl
  rcases (mem_closure_iff.mp hxZcl) D.carrier D.isOpen hxD with
    ⟨y, hyD, hyZ⟩
  exact hZ.subset hyZ (subset_closure hyD)

/--
%%handwave
name:
  A side-preserving collar lies in the domain and incident component closure
statement:
  Let \(W\cong S^1\times\mathbb R\) be a side-preserving collar, with
  \(t<0\) in \(D\) and \(t>0\) in the complementary component \(V\).
  Then
  \[
    W\subseteq D\cup\overline V.
  \]
proof:
  Split according to the sign of the collar coordinate.  Negative points lie
  in \(D\), positive points lie in \(V\), and zero-slice points are limits of
  the positive side and hence lie in \(\overline V\).
-/
theorem sidePreservingAnnularCollar_subset_carrier_union_componentClosure
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (hside : ∀ y : W, ((y : X) ∈ D.carrier ↔ (phi y).2 < 0))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (p : frontier D.carrier) (hpW : (p : X) ∈ W)
    (hpV : (p : X) ∈ frontier V) :
    (W : Set X) ⊆ D.carrier ∪ closure V := by
  intro x hxW
  let y : W := ⟨x, hxW⟩
  rcases lt_trichotomy (phi y).2 0 with hneg | hzero | hpos
  · exact Or.inl ((hside y).mpr hneg)
  · right
    have hyClosureHalf : x ∈
        closure ((W : Set X) ∩ (closure D.carrier)ᶜ) :=
      sidePreservingAnnularCollar_zeroSlice_mem_closure_exteriorSide
        D W phi hexteriorSide y hzero
    exact closure_mono
      (sidePreservingAnnularCollar_exteriorSide_subset_component
        D W phi hexteriorSide V hV p hpW hpV) hyClosureHalf
  · right
    apply subset_closure
    exact sidePreservingAnnularCollar_exteriorSide_subset_component
      D W phi hexteriorSide V hV p hpW hpV
        ⟨hxW, (hexteriorSide y).mpr hpos⟩

/--
%%handwave
name:
  An exterior collar-component union misses every other component closure
statement:
  Let \(V\ne Z\) be complementary components of a smooth boundary domain,
  and let \(W\) be a side-preserving collar incident to \(V\).  Then
  \((W\cup V)\cap\overline Z=\varnothing\).
proof:
  The collar-component union lies in \(D\cup\overline V\).  The domain is
  disjoint from \(\overline Z\), while an intersection of
  \(\overline V\) and \(\overline Z\) would force \(V=Z\).
-/
theorem exteriorComponentCollarUnion_disjoint_componentClosure_of_ne
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (hside : ∀ y : W, ((y : X) ∈ D.carrier ↔ (phi y).2 < 0))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V Z : Set X)
    (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (hZ : IsComponentOf Z (closure D.carrier)ᶜ)
    (p : frontier D.carrier) (hpW : (p : X) ∈ W)
    (hpV : (p : X) ∈ frontier V)
    (hne : V ≠ Z) :
    Disjoint
      (exteriorComponentCollarUnion W V
        (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl) : Set X)
      (closure Z) := by
  rw [Set.disjoint_left]
  intro x hxL hxZcl
  have hxDomainOrVClosure : x ∈ D.carrier ∪ closure V := by
    rcases hxL with hxW | hxV
    · exact sidePreservingAnnularCollar_subset_carrier_union_componentClosure
        D W phi hside hexteriorSide V hV p hpW hpV hxW
    · exact Or.inr (subset_closure hxV)
  rcases hxDomainOrVClosure with hxD | hxVcl
  · exact Set.disjoint_left.mp
      (smoothBoundaryDomain_carrier_disjoint_complement_component_closure
        D Z hZ) hxD hxZcl
  · apply hne
    exact smoothBoundaryDomain_complement_components_eq_of_closures_meet
      D V Z hV hZ ⟨x, hxVcl, hxZcl⟩

/-- The side-preserving annular-collar data attached to one complementary
component. -/
structure ComplementComponentCollarData
    (D : SmoothBoundaryDomain X)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ) where
  p : frontier D.carrier
  W : TopologicalSpace.Opens X
  phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ
  p_mem_frontier : (p : X) ∈ frontier V
  p_mem_collar : (p : X) ∈ W
  frontier_subset_collar : frontier V ⊆ (W : Set X)
  domain_side : ∀ y : W, ((y : X) ∈ D.carrier ↔ (phi y).2 < 0)
  exterior_side :
    ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2)

/--
%%handwave
name:
  Existence of side-preserving collar data for a complementary component
statement:
  Let \(X\) be a noncompact Riemann surface with vanishing first de Rham
  cohomology, and let \(D\) be a preconnected smooth relatively compact
  domain.  Every component \(V\) of \(X\setminus\overline D\) admits a full
  annular collar whose negative side is in \(D\), whose positive side is
  outside \(\overline D\), and which contains the frontier of \(V\).
proof:
  Apply the side-preserving annular-collar theorem for complementary
  components and package the boundary point, collar, chart, incidence, and
  side conditions into the stated data.
-/
theorem complementComponentCollarData_nonempty
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (hnoncompact : ¬ CompactSpace X)
    (D : SmoothBoundaryDomain X)
    (hDpre : IsPreconnected D.carrier)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ) :
    Nonempty (ComplementComponentCollarData D V hV) := by
  rcases exists_sidePreservingAnnularCollar_of_complementComponent
      hnoncompact D D.nonempty hDpre V hV with
    ⟨p, W, phi, hpV, hpW, hfrontierW, hside, hexterior⟩
  exact ⟨{
    p := p
    W := W
    phi := phi
    p_mem_frontier := hpV
    p_mem_collar := hpW
    frontier_subset_collar := hfrontierW
    domain_side := hside
    exterior_side := hexterior }⟩

/-! ## A cutoff representative of the angular class -/

/-- Connecting data for the locally constant step on the overlap of the two
punctured-cylinder charts. -/
noncomputable def annularAngularConnectingData (v : Circle) :
    DeRhamMayerVietorisConnectingData (I := AnnularCylinderModel) (A := ℝ)
      (annularPunctureOpen v) (annularPunctureOpen (annularOpposite v))
      (annularPunctures_cover v) 0 (annularOverlapStepClosedForm v) :=
  Classical.choice
    (deRham_mayerVietoris_connectingData_nonempty_of_partitionOfUnity
      (A := ℝ) AnnularCylinderModel
      (annularPunctureOpen v) (annularPunctureOpen (annularOpposite v))
      (annularPunctures_cover v) 0 (annularOverlapStepClosedForm v))

/-- Use the glued form in the connecting data as the angular representative.
This retains the local primitives needed for the period calculation. -/
noncomputable def annularAngularClosedForm (v : Circle) :
    DeRhamClosedForms (I := AnnularCylinderModel)
      (M := Circle × ℝ) (A := ℝ) 1 :=
  (annularAngularConnectingData v).glued

/--
%%handwave
name:
  Cohomology class of the chosen angular form
statement:
  The closed one-form obtained by gluing the Mayer--Vietoris local
  primitives represents the connecting class of the locally constant step
  function on the overlap of the two punctured-cylinder charts.
proof:
  This is the defining property of the partition-of-unity construction of
  the Mayer--Vietoris connecting form.
-/
theorem annularAngularClosedForm_class (v : Circle) :
    (DeRhamExactClosedForms (I := AnnularCylinderModel)
      (M := Circle × ℝ) (A := ℝ) 1).mkQ
        (annularAngularClosedForm v) = annularStepConnectingClass v := by
  symm
  exact deRhamMayerVietorisConnectingOfPartitionOfUnity_eq_mk_glued
    (A := ℝ) AnnularCylinderModel
    (annularPunctureOpen v) (annularPunctureOpen (annularOpposite v))
    (annularPunctures_cover v) 0 (annularOverlapStepClosedForm v)
    (annularAngularConnectingData v)

/-! ## A negative-half cycle detecting the angular class -/

/-- The punctured cylinder in its global stereographic product chart. -/
noncomputable def annularPuncturePlaneDiffeomorph (v : Circle) :
    annularPunctureOpen v ≃ₘ⟮AnnularCylinderModel,
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1) × ℝ)⟯
      (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1) × ℝ)) := by
  classical
  exact Classical.choice (by
    apply deRham_boundarylessExtendedChart_restriction_diffeomorph
      AnnularCylinderModel
      (e := annularPunctureChart v)
      (annularPunctureChart_mem_atlas v)
    · simpa [annularPunctureOpen, deRham_boundarylessExtendedChart] using
        ((annularPunctureChart v).extend_source
          (I := AnnularCylinderModel)).symm
    · intro y hy
      change y ∈ ((annularPunctureChart v).extend AnnularCylinderModel).target
      rw [OpenPartialHomeomorph.extend_target]
      simp [annularPunctureChart, AnnularCylinderModel]
      exact Set.mem_univ y)

/-- The affine smooth path between two points of a punctured cylinder, made
in the global stereographic product chart. -/
noncomputable def annularPunctureAffineSimplex (v : Circle)
    (a b : annularPunctureOpen v) :
    ContMDiffSingularSimplex
      (I := AnnularCylinderModel) (M := annularPunctureOpen v) 1 ∞ := by
  let psi := annularPuncturePlaneDiffeomorph v
  let G : SimplexAmbient 1 → EuclideanSpace ℝ (Fin 1) × ℝ :=
    fun q ↦ q 0 • (psi a : EuclideanSpace ℝ (Fin 1) × ℝ) +
      q 1 • (psi b : EuclideanSpace ℝ (Fin 1) × ℝ)
  let Gtop : SimplexAmbient 1 →
      (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1) × ℝ)) :=
    fun q ↦ ⟨G q, Set.mem_univ _⟩
  have hG : ContDiff ℝ ∞ G := by
    fun_prop
  have hGtop : ContMDiff (modelWithCornersSelf ℝ (SimplexAmbient 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1) × ℝ)) ∞ Gtop :=
    ContMDiff.codRestrict_open hG.contMDiff ⊤ (fun q ↦ Set.mem_univ _)
  let F : SimplexAmbient 1 → annularPunctureOpen v :=
    fun q ↦ psi.symm (Gtop q)
  have hF : ContMDiff (modelWithCornersSelf ℝ (SimplexAmbient 1))
      AnnularCylinderModel ∞ F :=
    psi.symm.contMDiff.comp hGtop
  exact
    { toContinuousMap :=
        ⟨fun q ↦ F q, hF.continuous.comp continuous_subtype_val⟩
      contMDiff := ⟨F, hF.contMDiffOn, fun _ ↦ rfl⟩ }

/--
%%handwave
name:
  Terminal face of the affine punctured-cylinder path
statement:
  For the affine one-simplex joining \(a\) to \(b\) in a global chart of a
  punctured cylinder, its zeroth face is \(b\).
proof:
  The zeroth face of the standard one-simplex has barycentric coordinates
  \((0,1)\), so the affine combination is \(b\).
-/
@[simp]
theorem annularPunctureAffineSimplex_face_zero_apply (v : Circle)
    (a b : annularPunctureOpen v) (q : StandardSimplex 0) :
    (annularPunctureAffineSimplex v a b).face 0 q = b := by
  have hq : (q : SimplexAmbient 0) 0 = 1 := by
    simpa using q.2.2
  change (annularPuncturePlaneDiffeomorph v).symm
      ⟨(simplexFaceMap 0 q : SimplexAmbient 1) 0 •
          ((annularPuncturePlaneDiffeomorph v) a :
            EuclideanSpace ℝ (Fin 1) × ℝ) +
        (simplexFaceMap 0 q : SimplexAmbient 1) 1 •
          ((annularPuncturePlaneDiffeomorph v) b :
            EuclideanSpace ℝ (Fin 1) × ℝ), Set.mem_univ _⟩ = b
  rw [show (simplexFaceMap 0 q : SimplexAmbient 1) 0 = 0 by
      exact simplexAmbientMap_succAbove_apply_omitted 0 q]
  rw [show (simplexFaceMap 0 q : SimplexAmbient 1) 1 =
      (q : SimplexAmbient 0) 0 by
      exact simplexAmbientMap_succAbove_apply_succAbove 0 q 0]
  simp [hq]

/--
%%handwave
name:
  Initial face of the affine punctured-cylinder path
statement:
  For the affine one-simplex joining \(a\) to \(b\) in a global chart of a
  punctured cylinder, its first face is \(a\).
proof:
  The first face has barycentric coordinates \((1,0)\), so the affine
  combination reduces to \(a\).
-/
@[simp]
theorem annularPunctureAffineSimplex_face_one_apply (v : Circle)
    (a b : annularPunctureOpen v) (q : StandardSimplex 0) :
    (annularPunctureAffineSimplex v a b).face 1 q = a := by
  have hq : (q : SimplexAmbient 0) 0 = 1 := by
    simpa using q.2.2
  change (annularPuncturePlaneDiffeomorph v).symm
      ⟨(simplexFaceMap 1 q : SimplexAmbient 1) 0 •
          ((annularPuncturePlaneDiffeomorph v) a :
            EuclideanSpace ℝ (Fin 1) × ℝ) +
        (simplexFaceMap 1 q : SimplexAmbient 1) 1 •
          ((annularPuncturePlaneDiffeomorph v) b :
            EuclideanSpace ℝ (Fin 1) × ℝ), Set.mem_univ _⟩ = a
  rw [show (simplexFaceMap 1 q : SimplexAmbient 1) 1 = 0 by
      exact simplexAmbientMap_succAbove_apply_omitted 1 q]
  rw [show (simplexFaceMap 1 q : SimplexAmbient 1) 0 =
      (q : SimplexAmbient 0) 0 by
      exact simplexAmbientMap_succAbove_apply_succAbove 1 q 0]
  simp [hq]

/-- Squeeze the normal coordinate of a punctured cylinder into the negative
half-line without changing its circle coordinate. -/
noncomputable def annularPunctureNegativeSqueezeMap (v : Circle) :
    C^∞⟮AnnularCylinderModel, annularPunctureOpen v;
      AnnularCylinderModel, annularPunctureOpen v⟯ := by
  let raw : annularPunctureOpen v → Circle × ℝ :=
    fun y ↦ ((y : Circle × ℝ).1, -Real.exp (y : Circle × ℝ).2)
  have hraw : ContMDiff AnnularCylinderModel AnnularCylinderModel ∞ raw := by
    have hval : ContMDiff AnnularCylinderModel AnnularCylinderModel ∞
        (fun y : annularPunctureOpen v ↦ (y : Circle × ℝ)) :=
      contMDiff_subtype_val
    exact hval.fst.prodMk (Real.contDiff_exp.neg.contMDiff.comp hval.snd)
  have hmem : ∀ y : annularPunctureOpen v, raw y ∈ annularPunctureOpen v := by
    intro y
    apply (mem_annularPunctureOpen_iff v (raw y)).mpr
    exact (mem_annularPunctureOpen_iff v (y : Circle × ℝ)).mp y.2
  exact ⟨fun y ↦ ⟨raw y, hmem y⟩,
    ContMDiff.codRestrict_open hraw (annularPunctureOpen v) hmem⟩

/-- The same squeeze, with codomain the negative half-cylinder. -/
noncomputable def annularPunctureToNegativeMap (v : Circle) :
    C^∞⟮AnnularCylinderModel, annularPunctureOpen v;
      AnnularCylinderModel, negativeAnnularCylinderOpen⟯ := by
  let raw : annularPunctureOpen v → Circle × ℝ :=
    fun y ↦ ((y : Circle × ℝ).1, -Real.exp (y : Circle × ℝ).2)
  have hraw : ContMDiff AnnularCylinderModel AnnularCylinderModel ∞ raw := by
    have hval : ContMDiff AnnularCylinderModel AnnularCylinderModel ∞
        (fun y : annularPunctureOpen v ↦ (y : Circle × ℝ)) :=
      contMDiff_subtype_val
    exact hval.fst.prodMk (Real.contDiff_exp.neg.contMDiff.comp hval.snd)
  have hmem : ∀ y : annularPunctureOpen v, raw y ∈ negativeAnnularCylinderOpen := by
    intro y
    exact ⟨Set.mem_univ _, neg_lt_zero.mpr (Real.exp_pos _)⟩
  exact ⟨fun y ↦ ⟨raw y, hmem y⟩,
    ContMDiff.codRestrict_open hraw negativeAnnularCylinderOpen hmem⟩

/-- A punctured-cylinder simplex squeezed toward the negative end, still
viewed in its punctured cylinder. -/
noncomputable def annularPunctureSqueezedSimplex (v : Circle)
    (sigma : ContMDiffSingularSimplex
      (I := AnnularCylinderModel) (M := annularPunctureOpen v) 1 ∞) :
    ContMDiffSingularSimplex
      (I := AnnularCylinderModel) (M := annularPunctureOpen v) 1 ∞ :=
  sigma.postcompose (I := AnnularCylinderModel)
    (annularPunctureNegativeSqueezeMap v)

/-- A punctured-cylinder simplex squeezed toward the negative end and viewed
as a simplex of the negative half-cylinder. -/
noncomputable def annularNegativeSimplexOfPuncture (v : Circle)
    (sigma : ContMDiffSingularSimplex
      (I := AnnularCylinderModel) (M := annularPunctureOpen v) 1 ∞) :
    ContMDiffSingularSimplex
      (I := AnnularCylinderModel) (M := negativeAnnularCylinderOpen) 1 ∞ :=
  sigma.postcompose (I := AnnularCylinderModel)
    (annularPunctureToNegativeMap v)

/--
%%handwave
name:
  Value of a squeezed punctured-cylinder simplex
statement:
  Squeezing a simplex \(\sigma\) toward the negative end sends
  \(\sigma(q)=(z,t)\) to \((z,-e^t)\).
proof:
  This is the pointwise definition of postcomposition by the negative
  squeeze map.
-/
@[simp]
theorem annularPunctureSqueezedSimplex_apply (v : Circle)
    (sigma : ContMDiffSingularSimplex
      (I := AnnularCylinderModel) (M := annularPunctureOpen v) 1 ∞)
    (q : StandardSimplex 1) :
    ((annularPunctureSqueezedSimplex v sigma q :
        annularPunctureOpen v) : Circle × ℝ) =
      ((sigma q : Circle × ℝ).1, -Real.exp (sigma q : Circle × ℝ).2) :=
  rfl

/--
%%handwave
name:
  Value of the negative-half simplex associated to a punctured simplex
statement:
  Viewing the negatively squeezed simplex in the negative half-cylinder
  sends \(\sigma(q)=(z,t)\) to \((z,-e^t)\).
proof:
  This is the definition of the postcomposition map into the negative
  half-cylinder.
-/
@[simp]
theorem annularNegativeSimplexOfPuncture_apply (v : Circle)
    (sigma : ContMDiffSingularSimplex
      (I := AnnularCylinderModel) (M := annularPunctureOpen v) 1 ∞)
    (q : StandardSimplex 1) :
    ((annularNegativeSimplexOfPuncture v sigma q :
        negativeAnnularCylinderOpen) : Circle × ℝ) =
      ((sigma q : Circle × ℝ).1, -Real.exp (sigma q : Circle × ℝ).2) :=
  rfl

/--
%%handwave
name:
  Difference of the two angular local primitives
statement:
  On the double-puncture overlap, the value of the first local primitive
  minus the value of the second is the locally constant overlap step
  function.
proof:
  Evaluate the Mayer--Vietoris lift-difference identity at the point.  For
  zero-forms, restriction merely evaluates the same scalar at the included
  point, yielding the stated pointwise formula.
-/
theorem annularAngularLift_difference_apply (v : Circle)
    (x : annularDoublePunctureOpen v) :
    (annularAngularConnectingData v).lift.1.toFun
          (TopologicalSpace.Opens.inclusion inf_le_left x)
          (fun i : Fin 0 => nomatch i) -
        (annularAngularConnectingData v).lift.2.toFun
          (TopologicalSpace.Opens.inclusion inf_le_right x)
          (fun i : Fin 0 => nomatch i) =
      annularOverlapStepFunction v x := by
  have h := congrArg
    (fun omega : SmoothForms (I := AnnularCylinderModel)
        (M := annularDoublePunctureOpen v) ℝ 0 =>
      omega.toFun x (fun i : Fin 0 => nomatch i))
    (annularAngularConnectingData v).lift_difference
  simp only [deRhamMayerVietorisSmoothDifference,
    annularOverlapStepClosedForm, smoothRealFunctionToZeroForm,
    smoothRealFunctionOfIsLocallyConstant,
    ContinuousAlternatingMap.constOfIsEmpty_apply] at h
  have hleft :
      (restrictSmoothFormsOfLE (I := AnnularCylinderModel) (A := ℝ)
          (W := annularDoublePunctureOpen v)
          (V := annularPunctureOpen v) inf_le_left 0
          (annularAngularConnectingData v).lift.1).toFun x
            (fun i : Fin 0 => nomatch i) =
        (annularAngularConnectingData v).lift.1.toFun
          (TopologicalSpace.Opens.inclusion inf_le_left x)
          (fun i : Fin 0 => nomatch i) := by
    change
      ((annularAngularConnectingData v).lift.1.toFun
        (TopologicalSpace.Opens.inclusion inf_le_left x)).compContinuousLinearMap _
          (fun i : Fin 0 => nomatch i) = _
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact Fin.elim0 i
  have hright :
      (restrictSmoothFormsOfLE (I := AnnularCylinderModel) (A := ℝ)
          (W := annularDoublePunctureOpen v)
          (V := annularPunctureOpen (annularOpposite v)) inf_le_right 0
          (annularAngularConnectingData v).lift.2).toFun x
            (fun i : Fin 0 => nomatch i) =
        (annularAngularConnectingData v).lift.2.toFun
          (TopologicalSpace.Opens.inclusion inf_le_right x)
          (fun i : Fin 0 => nomatch i) := by
    change
      ((annularAngularConnectingData v).lift.2.toFun
        (TopologicalSpace.Opens.inclusion inf_le_right x)).compContinuousLinearMap _
          (fun i : Fin 0 => nomatch i) = _
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact Fin.elim0 i
  change
    (restrictSmoothFormsOfLE (I := AnnularCylinderModel) (A := ℝ)
          (W := annularDoublePunctureOpen v)
          (V := annularPunctureOpen v) inf_le_left 0
          (annularAngularConnectingData v).lift.1).toFun x
            (fun i : Fin 0 => nomatch i) -
        (restrictSmoothFormsOfLE (I := AnnularCylinderModel) (A := ℝ)
          (W := annularDoublePunctureOpen v)
          (V := annularPunctureOpen (annularOpposite v)) inf_le_right 0
          (annularAngularConnectingData v).lift.2).toFun x
            (fun i : Fin 0 => nomatch i) =
      annularOverlapStepFunction v x at h
  rw [hleft, hright] at h
  exact h

/--
%%handwave
name:
  Integral of the angular form on a squeezed path in the first chart
statement:
  On the first punctured-cylinder chart, the integral of the chosen angular
  form along a negatively squeezed path equals the value of the first local
  primitive at the terminal face minus its value at the initial face.
proof:
  The glued angular form restricts on this chart to the exterior derivative
  of the first primitive.  Apply the fundamental theorem for the integral of
  an exact one-form over a smooth one-simplex.
-/
theorem integrate_annularAngularClosedForm_left_squeezed (v : Circle)
    (sigma : ContMDiffSingularSimplex
      (I := AnnularCylinderModel) (M := annularPunctureOpen v) 1 ∞) :
    integrateSmoothChain (I := AnnularCylinderModel)
        (annularAngularClosedForm v).1
        (Finsupp.single
          ((annularPunctureSqueezedSimplex v sigma).openInclusion
            (I := AnnularCylinderModel) (annularPunctureOpen v)) (1 : ℤ)) =
      (annularAngularConnectingData v).lift.1.toFun
          ((annularPunctureSqueezedSimplex v sigma).face 0
            standardZeroSimplexVertex)
          (fun i : Fin 0 => nomatch i) -
        (annularAngularConnectingData v).lift.1.toFun
          ((annularPunctureSqueezedSimplex v sigma).face 1
            standardZeroSimplexVertex)
          (fun i : Fin 0 => nomatch i) := by
  rw [integrateSmoothChain_openInclusion_single]
  have hrest := congrArg Prod.fst
    (annularAngularConnectingData v).glued_restriction
  change restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
      (annularPunctureOpen v) 1 (annularAngularClosedForm v).1 =
    deRhamDifferential (I := AnnularCylinderModel)
      (M := annularPunctureOpen v) (A := ℝ) 0
        (annularAngularConnectingData v).lift.1 at hrest
  rw [hrest]
  exact integrateSmoothChain_deRhamDifferential_zeroForm_single_eq_endpoint_sub
    (I := AnnularCylinderModel) (annularAngularConnectingData v).lift.1
      (annularPunctureSqueezedSimplex v sigma)

/--
%%handwave
name:
  Integral of the angular form on a squeezed path in the second chart
statement:
  On the opposite punctured-cylinder chart, the integral of the chosen
  angular form along a negatively squeezed path is the endpoint difference
  of the second local primitive.
proof:
  The glued angular form restricts here to the derivative of the second
  primitive.  The integral of this exact one-form over the simplex is its
  terminal value minus its initial value.
-/
theorem integrate_annularAngularClosedForm_right_squeezed (v : Circle)
    (sigma : ContMDiffSingularSimplex
      (I := AnnularCylinderModel)
      (M := annularPunctureOpen (annularOpposite v)) 1 ∞) :
    integrateSmoothChain (I := AnnularCylinderModel)
        (annularAngularClosedForm v).1
        (Finsupp.single
          ((annularPunctureSqueezedSimplex (annularOpposite v) sigma).openInclusion
            (I := AnnularCylinderModel)
              (annularPunctureOpen (annularOpposite v))) (1 : ℤ)) =
      (annularAngularConnectingData v).lift.2.toFun
          ((annularPunctureSqueezedSimplex (annularOpposite v) sigma).face 0
            standardZeroSimplexVertex)
          (fun i : Fin 0 => nomatch i) -
        (annularAngularConnectingData v).lift.2.toFun
          ((annularPunctureSqueezedSimplex (annularOpposite v) sigma).face 1
            standardZeroSimplexVertex)
          (fun i : Fin 0 => nomatch i) := by
  rw [integrateSmoothChain_openInclusion_single]
  have hrest := congrArg Prod.snd
    (annularAngularConnectingData v).glued_restriction
  change restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
      (annularPunctureOpen (annularOpposite v)) 1
        (annularAngularClosedForm v).1 =
    deRhamDifferential (I := AnnularCylinderModel)
      (M := annularPunctureOpen (annularOpposite v)) (A := ℝ) 0
        (annularAngularConnectingData v).lift.2 at hrest
  rw [hrest]
  exact integrateSmoothChain_deRhamDifferential_zeroForm_single_eq_endpoint_sub
    (I := AnnularCylinderModel) (annularAngularConnectingData v).lift.2
      (annularPunctureSqueezedSimplex (annularOpposite v) sigma)

/-- Squeeze a point of the double-puncture overlap into the negative
half-cylinder. -/
noncomputable def annularOverlapNegativeSqueeze (v : Circle)
    (x : annularDoublePunctureOpen v) : annularDoublePunctureOpen v := by
  refine ⟨((x : Circle × ℝ).1, -Real.exp (x : Circle × ℝ).2), ?_⟩
  change
    ((x : Circle × ℝ).1, -Real.exp (x : Circle × ℝ).2) ∈
        annularPunctureOpen v ∧
      ((x : Circle × ℝ).1, -Real.exp (x : Circle × ℝ).2) ∈
        annularPunctureOpen (annularOpposite v)
  exact ⟨
    (mem_annularPunctureOpen_iff v _).mpr
      ((mem_annularPunctureOpen_iff v (x : Circle × ℝ)).mp x.2.1),
    (mem_annularPunctureOpen_iff (annularOpposite v) _).mpr
      ((mem_annularPunctureOpen_iff (annularOpposite v)
        (x : Circle × ℝ)).mp x.2.2)⟩

/--
%%handwave
name:
  Compatibility of negative squeezing with the first overlap inclusion
statement:
  Including a negatively squeezed overlap point into the first punctured
  cylinder equals first including the point and then applying the negative
  squeeze there.
proof:
  Both maps have the same underlying cylinder point \((z,t)\mapsto(z,-e^t)\).
-/
@[simp]
theorem annularOverlapNegativeSqueeze_inclusion_left (v : Circle)
    (x : annularDoublePunctureOpen v) :
    TopologicalSpace.Opens.inclusion inf_le_left
        (annularOverlapNegativeSqueeze v x) =
      annularPunctureNegativeSqueezeMap v
        (TopologicalSpace.Opens.inclusion inf_le_left x) := by
  apply Subtype.ext
  rfl

/--
%%handwave
name:
  Compatibility of negative squeezing with the second overlap inclusion
statement:
  Including a negatively squeezed overlap point into the opposite punctured
  cylinder equals including first and then applying its negative squeeze.
proof:
  Both constructions send \((z,t)\) to the same point \((z,-e^t)\).
-/
@[simp]
theorem annularOverlapNegativeSqueeze_inclusion_right (v : Circle)
    (x : annularDoublePunctureOpen v) :
    TopologicalSpace.Opens.inclusion inf_le_right
        (annularOverlapNegativeSqueeze v x) =
      annularPunctureNegativeSqueezeMap (annularOpposite v)
        (TopologicalSpace.Opens.inclusion inf_le_right x) := by
  apply Subtype.ext
  rfl

/--
%%handwave
name:
  The overlap step remains one after squeezing the positive angular component
statement:
  If a point lies in the positive connected component of the double-puncture
  overlap, then its negative radial squeeze still lies in that component and
  the overlap step function has value \(1\) there.
proof:
  The squeeze changes only the radial coordinate, so it preserves the angular
  component.  The step function is defined to be one on the positive
  component.
-/
theorem annularOverlapStepFunction_negativeSqueeze_positive (v : Circle)
    (x : annularPositiveComponent v) :
    annularOverlapStepFunction v
      (annularOverlapNegativeSqueeze v
        (TopologicalSpace.Opens.inclusion
          (annularPositiveComponent_le_doublePuncture v) x)) = 1 := by
  let xOverlap : annularDoublePunctureOpen v :=
    TopologicalSpace.Opens.inclusion
      (annularPositiveComponent_le_doublePuncture v) x
  have hpos : annularOverlapNegativeSqueeze v xOverlap ∈
      annularOverlapPositiveSet v := by
    change ((annularOverlapNegativeSqueeze v xOverlap :
      annularDoublePunctureOpen v) : Circle × ℝ) ∈
        (annularPositiveComponent v : Set (Circle × ℝ))
    apply (mem_annularPositiveComponent_iff v _).mpr
    simpa [annularOverlapNegativeSqueeze, xOverlap] using
      ((mem_annularPositiveComponent_iff v (x : Circle × ℝ)).mp x.2)
  change annularOverlapStepFunction v
    (annularOverlapNegativeSqueeze v xOverlap) = 1
  simp [annularOverlapStepFunction, hpos]

/--
%%handwave
name:
  The overlap step remains zero after squeezing the negative angular component
statement:
  If a point lies in the negative connected component of the double-puncture
  overlap, then its negative radial squeeze has overlap step value \(0\).
proof:
  Radial squeezing preserves the angular component, hence preserves the
  negative component.  The two angular components are disjoint, so the
  squeezed point is not in the positive component where the step equals one.
-/
theorem annularOverlapStepFunction_negativeSqueeze_negative (v : Circle)
    (x : annularNegativeComponent v) :
    annularOverlapStepFunction v
      (annularOverlapNegativeSqueeze v
        (TopologicalSpace.Opens.inclusion
          (annularNegativeComponent_le_doublePuncture v) x)) = 0 := by
  let xOverlap : annularDoublePunctureOpen v :=
    TopologicalSpace.Opens.inclusion
      (annularNegativeComponent_le_doublePuncture v) x
  have hneg : ((annularOverlapNegativeSqueeze v xOverlap :
      annularDoublePunctureOpen v) : Circle × ℝ) ∈
        (annularNegativeComponent v : Set (Circle × ℝ)) := by
    apply (mem_annularNegativeComponent_iff v _).mpr
    simpa [annularOverlapNegativeSqueeze, xOverlap] using
      ((mem_annularNegativeComponent_iff v (x : Circle × ℝ)).mp x.2)
  have hnot : annularOverlapNegativeSqueeze v xOverlap ∉
      annularOverlapPositiveSet v := by
    intro hpos
    have hmem : ((annularOverlapNegativeSqueeze v xOverlap :
        annularDoublePunctureOpen v) : Circle × ℝ) ∈
        (annularPositiveComponent v ⊓ annularNegativeComponent v :
          TopologicalSpace.Opens (Circle × ℝ)) := ⟨hpos, hneg⟩
    rw [annularComponents_disjoint v] at hmem
    exact hmem
  change annularOverlapStepFunction v
    (annularOverlapNegativeSqueeze v xOverlap) = 0
  simp [annularOverlapStepFunction, hnot]

/--
%%handwave
name:
  A negative annular cycle with angular period minus one
statement:
  For every deleted direction \(v\in S^1\), there is a smooth one-cycle
  \(c\) contained in \(S^1\times(-\infty,0)\) such that the chosen angular
  form satisfies
  \[
    \partial c=0,\qquad \int_c\omega_v=-1.
  \]
proof:
  Join a point of the positive overlap component to a point of the negative
  component in the first punctured chart, return in the second chart, and
  squeeze both paths into the negative half-cylinder.  Their endpoints
  cancel.  The two exact-chart integrals telescope to the difference of the
  overlap step values, namely \(0-1=-1\).
-/
theorem exists_negativeAnnularCycle_angular_period_eq_neg_one (v : Circle) :
    ∃ c : SingularChain (I := AnnularCylinderModel)
        (M := negativeAnnularCylinderOpen) 1 ∞,
      boundary (I := AnnularCylinderModel) c = 0 ∧
        integrateSmoothChain (I := AnnularCylinderModel)
          (restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
            negativeAnnularCylinderOpen 1 (annularAngularClosedForm v).1) c = -1 := by
  classical
  let aPos : annularPositiveComponent v :=
    Classical.choice (annularPositiveComponent_nonempty v)
  let bNeg : annularNegativeComponent v :=
    Classical.choice (annularNegativeComponent_nonempty v)
  let a : annularDoublePunctureOpen v :=
    TopologicalSpace.Opens.inclusion
      (annularPositiveComponent_le_doublePuncture v) aPos
  let b : annularDoublePunctureOpen v :=
    TopologicalSpace.Opens.inclusion
      (annularNegativeComponent_le_doublePuncture v) bNeg
  let aU : annularPunctureOpen v :=
    TopologicalSpace.Opens.inclusion inf_le_left a
  let bU : annularPunctureOpen v :=
    TopologicalSpace.Opens.inclusion inf_le_left b
  let aV : annularPunctureOpen (annularOpposite v) :=
    TopologicalSpace.Opens.inclusion inf_le_right a
  let bV : annularPunctureOpen (annularOpposite v) :=
    TopologicalSpace.Opens.inclusion inf_le_right b
  let sigmaU := annularPunctureAffineSimplex v aU bU
  let sigmaV := annularPunctureAffineSimplex (annularOpposite v) bV aV
  let tauU := annularNegativeSimplexOfPuncture v sigmaU
  let tauV := annularNegativeSimplexOfPuncture (annularOpposite v) sigmaV
  let c : SingularChain (I := AnnularCylinderModel)
      (M := negativeAnnularCylinderOpen) 1 ∞ :=
    Finsupp.single tauU (1 : ℤ) + Finsupp.single tauV (1 : ℤ)
  let aN : negativeAnnularCylinderOpen := annularPunctureToNegativeMap v aU
  let bN : negativeAnnularCylinderOpen := annularPunctureToNegativeMap v bU
  have htauU0 : tauU.face 0 =
      ContMDiffSingularSimplex.point (I := AnnularCylinderModel) bN := by
    apply ContMDiffSingularSimplex.ext_apply
    intro q
    change annularPunctureToNegativeMap v
      ((annularPunctureAffineSimplex v aU bU).face 0 q) = bN
    rw [annularPunctureAffineSimplex_face_zero_apply]
  have htauU1 : tauU.face 1 =
      ContMDiffSingularSimplex.point (I := AnnularCylinderModel) aN := by
    apply ContMDiffSingularSimplex.ext_apply
    intro q
    change annularPunctureToNegativeMap v
      ((annularPunctureAffineSimplex v aU bU).face 1 q) = aN
    rw [annularPunctureAffineSimplex_face_one_apply]
  have htauV0 : tauV.face 0 =
      ContMDiffSingularSimplex.point (I := AnnularCylinderModel) aN := by
    apply ContMDiffSingularSimplex.ext_apply
    intro q
    change annularPunctureToNegativeMap (annularOpposite v)
      ((annularPunctureAffineSimplex (annularOpposite v) bV aV).face 0 q) = aN
    rw [annularPunctureAffineSimplex_face_zero_apply]
    apply Subtype.ext
    rfl
  have htauV1 : tauV.face 1 =
      ContMDiffSingularSimplex.point (I := AnnularCylinderModel) bN := by
    apply ContMDiffSingularSimplex.ext_apply
    intro q
    change annularPunctureToNegativeMap (annularOpposite v)
      ((annularPunctureAffineSimplex (annularOpposite v) bV aV).face 1 q) = bN
    rw [annularPunctureAffineSimplex_face_one_apply]
    apply Subtype.ext
    rfl
  have hcycle : boundary (I := AnnularCylinderModel) c = 0 := by
    simp [c, boundary, htauU0, htauU1, htauV0, htauV1]
  refine ⟨c, hcycle, ?_⟩
  let aS := annularOverlapNegativeSqueeze v a
  let bS := annularOverlapNegativeSqueeze v b
  have hsigmaU0 :
      (annularPunctureSqueezedSimplex v sigmaU).face 0
          standardZeroSimplexVertex =
        TopologicalSpace.Opens.inclusion inf_le_left bS := by
    change annularPunctureNegativeSqueezeMap v
      ((annularPunctureAffineSimplex v aU bU).face 0
        standardZeroSimplexVertex) = _
    rw [annularPunctureAffineSimplex_face_zero_apply]
    exact (annularOverlapNegativeSqueeze_inclusion_left v b).symm
  have hsigmaU1 :
      (annularPunctureSqueezedSimplex v sigmaU).face 1
          standardZeroSimplexVertex =
        TopologicalSpace.Opens.inclusion inf_le_left aS := by
    change annularPunctureNegativeSqueezeMap v
      ((annularPunctureAffineSimplex v aU bU).face 1
        standardZeroSimplexVertex) = _
    rw [annularPunctureAffineSimplex_face_one_apply]
    exact (annularOverlapNegativeSqueeze_inclusion_left v a).symm
  have hsigmaV0 :
      (annularPunctureSqueezedSimplex (annularOpposite v) sigmaV).face 0
          standardZeroSimplexVertex =
        TopologicalSpace.Opens.inclusion inf_le_right aS := by
    change annularPunctureNegativeSqueezeMap (annularOpposite v)
      ((annularPunctureAffineSimplex (annularOpposite v) bV aV).face 0
        standardZeroSimplexVertex) = _
    rw [annularPunctureAffineSimplex_face_zero_apply]
    exact (annularOverlapNegativeSqueeze_inclusion_right v a).symm
  have hsigmaV1 :
      (annularPunctureSqueezedSimplex (annularOpposite v) sigmaV).face 1
          standardZeroSimplexVertex =
        TopologicalSpace.Opens.inclusion inf_le_right bS := by
    change annularPunctureNegativeSqueezeMap (annularOpposite v)
      ((annularPunctureAffineSimplex (annularOpposite v) bV aV).face 1
        standardZeroSimplexVertex) = _
    rw [annularPunctureAffineSimplex_face_one_apply]
    exact (annularOverlapNegativeSqueeze_inclusion_right v b).symm
  have hleft := integrate_annularAngularClosedForm_left_squeezed v sigmaU
  rw [hsigmaU0, hsigmaU1] at hleft
  have hright := integrate_annularAngularClosedForm_right_squeezed v sigmaV
  rw [hsigmaV0, hsigmaV1] at hright
  have hdiffA := annularAngularLift_difference_apply v aS
  have hdiffB := annularAngularLift_difference_apply v bS
  have hstepA : annularOverlapStepFunction v aS = 1 := by
    simpa [aS, a] using
      annularOverlapStepFunction_negativeSqueeze_positive v aPos
  have hstepB : annularOverlapStepFunction v bS = 0 := by
    simpa [bS, b] using
      annularOverlapStepFunction_negativeSqueeze_negative v bNeg
  let sigmaUAmbient :=
    (annularPunctureSqueezedSimplex v sigmaU).openInclusion
      (I := AnnularCylinderModel) (annularPunctureOpen v)
  let sigmaVAmbient :=
    (annularPunctureSqueezedSimplex (annularOpposite v) sigmaV).openInclusion
      (I := AnnularCylinderModel)
        (annularPunctureOpen (annularOpposite v))
  let cAmbient : SingularChain (I := AnnularCylinderModel)
      (M := Circle × ℝ) 1 ∞ :=
    Finsupp.single sigmaUAmbient (1 : ℤ) +
      Finsupp.single sigmaVAmbient (1 : ℤ)
  have hglobal :
      integrateSmoothChain (I := AnnularCylinderModel)
        (annularAngularClosedForm v).1 cAmbient = -1 := by
    rw [integrateSmoothChain_add]
    change
      integrateSmoothChain (I := AnnularCylinderModel)
          (annularAngularClosedForm v).1
          (Finsupp.single
            ((annularPunctureSqueezedSimplex v sigmaU).openInclusion
              (I := AnnularCylinderModel) (annularPunctureOpen v)) (1 : ℤ)) +
        integrateSmoothChain (I := AnnularCylinderModel)
          (annularAngularClosedForm v).1
          (Finsupp.single
            ((annularPunctureSqueezedSimplex (annularOpposite v) sigmaV).openInclusion
              (I := AnnularCylinderModel)
                (annularPunctureOpen (annularOpposite v))) (1 : ℤ)) = -1
    rw [hleft, hright]
    rw [hstepA] at hdiffA
    rw [hstepB] at hdiffB
    linarith
  have htauUAmbient :
      tauU.openInclusion (I := AnnularCylinderModel) negativeAnnularCylinderOpen =
        sigmaUAmbient := by
    apply ContMDiffSingularSimplex.ext_apply
    intro q
    rfl
  have htauVAmbient :
      tauV.openInclusion (I := AnnularCylinderModel) negativeAnnularCylinderOpen =
        sigmaVAmbient := by
    apply ContMDiffSingularSimplex.ext_apply
    intro q
    rfl
  have hcAmbient :
      SingularChain.openInclusion (I := AnnularCylinderModel)
        negativeAnnularCylinderOpen c = cAmbient := by
    simp [c, cAmbient, SingularChain.openInclusion_add,
      htauUAmbient, htauVAmbient]
  calc
    integrateSmoothChain (I := AnnularCylinderModel)
        (restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
          negativeAnnularCylinderOpen 1 (annularAngularClosedForm v).1) c =
      integrateSmoothChain (I := AnnularCylinderModel)
        (annularAngularClosedForm v).1
        (SingularChain.openInclusion (I := AnnularCylinderModel)
          negativeAnnularCylinderOpen c) :=
      (integrateSmoothChain_openInclusion
        (I := AnnularCylinderModel) negativeAnnularCylinderOpen
        (annularAngularClosedForm v).1 c).symm
    _ = integrateSmoothChain (I := AnnularCylinderModel)
        (annularAngularClosedForm v).1 cAmbient := by rw [hcAmbient]
    _ = -1 := hglobal

/--
%%handwave
name:
  The angular class is nonzero on a half-cylinder
statement:
  Let \(d\theta\) denote the normalized angular closed one-form on
  \(S^1\times\mathbb R\).  Its restriction to
  \(S^1\times(-\infty,0)\) represents a nonzero class in
  \[
    H^1_{\mathrm{dR}}\bigl(S^1\times(-\infty,0);\mathbb R\bigr).
  \]
proof:
  A negatively oriented circle contained in the negative half-cylinder is a
  smooth cycle on which the restricted angular form has integral \(-1\).
  Hence the form has nonzero period and cannot be exact.
-/
theorem annularAngularClosedForm_negative_class_ne_zero (v : Circle) :
    (DeRhamExactClosedForms (I := AnnularCylinderModel)
      (M := negativeAnnularCylinderOpen) (A := ℝ) 1).mkQ
        (deRhamClosedFormsRestrictionToOpen (I := AnnularCylinderModel)
          (A := ℝ) negativeAnnularCylinderOpen 1
            (annularAngularClosedForm v)) ≠ 0 := by
  rcases exists_negativeAnnularCycle_angular_period_eq_neg_one v with
    ⟨c, hcycle, hperiod⟩
  apply deRhamCohomologyClass_ne_zero_of_nonzero_period
    (I := AnnularCylinderModel)
    (deRhamClosedFormsRestrictionToOpen (I := AnnularCylinderModel)
      (A := ℝ) negativeAnnularCylinderOpen 1 (annularAngularClosedForm v))
    c hcycle
  change
    integrateSmoothChain (I := AnnularCylinderModel)
      (restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
        negativeAnnularCylinderOpen 1 (annularAngularClosedForm v).1) c ≠ 0
  rw [hperiod]
  norm_num

/-- A smooth cutoff which is one on the nonpositive half-line and zero from
one onward. -/
def annularExteriorCutoff (t : ℝ) : ℝ :=
  1 - Real.smoothTransition (2 * t - 1)

/--
%%handwave
name:
  Smoothness of the exterior cutoff
statement:
  The function \(\rho(t)=1-\sigma(2t-1)\), where \(\sigma\) is the standard
  smooth transition function, is smooth on \(\mathbb R\).
proof:
  Smoothness follows by composition of the smooth transition function with
  the affine map \(t\mapsto2t-1\), followed by subtraction from the constant
  function one.
-/
@[fun_prop]
theorem contDiff_annularExteriorCutoff :
    ContDiff ℝ ∞ annularExteriorCutoff := by
  exact contDiff_const.sub
    (Real.smoothTransition.contDiff.comp
      (contDiff_const.mul contDiff_id |>.sub contDiff_const))

/--
%%handwave
name:
  The exterior cutoff equals one before the midpoint
statement:
  If \(t\le\tfrac12\), then \(\rho(t)=1\).
proof:
  In this range \(2t-1\le0\), so the standard smooth transition function
  vanishes.
-/
@[simp]
theorem annularExteriorCutoff_eq_one_of_le_half {t : ℝ}
    (ht : t ≤ 1 / 2) :
    annularExteriorCutoff t = 1 := by
  apply sub_eq_self.mpr
  apply Real.smoothTransition.zero_of_nonpos
  linarith

/--
%%handwave
name:
  The exterior cutoff equals one on the nonpositive half-line
statement:
  If \(t\le0\), then \(\rho(t)=1\).
proof:
  This is the preceding midpoint identity, since \(t\le0\le\tfrac12\).
-/
@[simp]
theorem annularExteriorCutoff_eq_one_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    annularExteriorCutoff t = 1 := by
  exact annularExteriorCutoff_eq_one_of_le_half (ht.trans (by norm_num))

/--
%%handwave
name:
  The exterior cutoff vanishes after one
statement:
  If \(t\ge1\), then \(\rho(t)=0\).
proof:
  Here \(2t-1\ge1\), so the standard smooth transition function equals one.
-/
@[simp]
theorem annularExteriorCutoff_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    annularExteriorCutoff t = 0 := by
  simp only [annularExteriorCutoff, sub_eq_zero]
  symm
  apply Real.smoothTransition.one_of_one_le
  linarith

/-- The exterior-side cutoff as a smooth function on the standard cylinder. -/
noncomputable def annularExteriorCutoffFunction :
    C^∞⟮AnnularCylinderModel, Circle × ℝ; ℝ⟯ where
  val := fun p ↦ annularExteriorCutoff p.2
  property := contDiff_annularExteriorCutoff.contMDiff.comp contMDiff_snd

/--
%%handwave
name:
  Value of the cylindrical exterior cutoff
statement:
  At \((z,t)\in S^1\times\mathbb R\), the cylindrical cutoff function has
  value \(\rho(t)\).
proof:
  This is its definition as the pullback of \(\rho\) along the second
  projection.
-/
@[simp]
theorem annularExteriorCutoffFunction_apply (p : Circle × ℝ) :
    annularExteriorCutoffFunction p = annularExteriorCutoff p.2 :=
  rfl

/-- Cut off the angular representative only toward the positive end. -/
noncomputable def annularCutoffAngularOneForm (v : Circle) :
    SmoothForms (I := AnnularCylinderModel) (M := Circle × ℝ) ℝ 1 :=
  smoothFormsPointwiseSMul (I := AnnularCylinderModel) (A := ℝ)
    annularExteriorCutoffFunction (annularAngularClosedForm v).1

/-- The compact cylinder band containing the derivative defect of the cutoff
angular form. -/
def annularCutoffAngularCore : Set (Circle × ℝ) :=
  (univ : Set Circle) ×ˢ Icc (1 / 2 : ℝ) 1

/--
%%handwave
name:
  Compactness of the angular cutoff defect band
statement:
  The cylinder band \(S^1\times[\tfrac12,1]\), containing the derivative of
  the cutoff, is compact.
proof:
  It is the product of the compact circle with a compact interval.
-/
theorem annularCutoffAngularCore_isCompact :
    IsCompact annularCutoffAngularCore := by
  exact isCompact_univ.prod isCompact_Icc

/--
%%handwave
name:
  The cutoff angular form is closed outside its transition band
statement:
  For the one-form \(\rho(t)\,d\theta\) on
  \(S^1\times\mathbb R\), its exterior derivative vanishes at every point
  outside \(S^1\times[\tfrac12,1]\).
proof:
  Below \(t=\tfrac12\), the cutoff is locally one and the form is the closed
  angular form.  Above \(t=1\), it is locally zero.  Locality of the exterior
  derivative gives the result in both cases.
-/
theorem annularCutoffAngularOneForm_derivative_eq_zero_of_not_mem_core
    (v : Circle) (p : Circle × ℝ) (hp : p ∉ annularCutoffAngularCore) :
    (deRhamDifferential (I := AnnularCylinderModel)
      (M := Circle × ℝ) (A := ℝ) 1
        (annularCutoffAngularOneForm v)).toFun p = 0 := by
  have hp' : p.2 < 1 / 2 ∨ 1 < p.2 := by
    by_cases hpneg : p.2 < 1 / 2
    · exact Or.inl hpneg
    · refine Or.inr (lt_of_not_ge ?_)
      intro hpone
      exact hp ⟨mem_univ _, le_of_not_gt hpneg, hpone⟩
  rcases hp' with hpneg | hppos
  · have hlocal : ∀ᶠ q in nhds p,
        (annularCutoffAngularOneForm v).toFun q =
          (annularAngularClosedForm v).1.toFun q := by
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hpneg]
        with q hq
      simp [annularCutoffAngularOneForm,
        annularExteriorCutoff_eq_one_of_le_half hq.le]
    rw [deRhamDifferential_toFun_eq_of_eventuallyEq
      (I := AnnularCylinderModel) (annularCutoffAngularOneForm v)
      (annularAngularClosedForm v).1 hlocal]
    exact congrArg (fun omega ↦ omega.toFun p) (annularAngularClosedForm v).2
  · have hlocal : ∀ᶠ q in nhds p,
        (annularCutoffAngularOneForm v).toFun q =
          (0 : SmoothForms (I := AnnularCylinderModel)
            (M := Circle × ℝ) ℝ 1).toFun q := by
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hppos]
        with q hq
      simp [annularCutoffAngularOneForm,
        annularExteriorCutoff_eq_zero_of_one_le hq.le]
    rw [deRhamDifferential_toFun_eq_of_eventuallyEq
      (I := AnnularCylinderModel) (annularCutoffAngularOneForm v) 0 hlocal]
    have hzero : deRhamDifferential (I := AnnularCylinderModel)
        (M := Circle × ℝ) (A := ℝ) 1
          (0 : SmoothForms (I := AnnularCylinderModel)
            (M := Circle × ℝ) ℝ 1) = 0 := LinearMap.map_zero _
    exact congrArg (fun omega ↦ omega.toFun p) hzero

/--
%%handwave
name:
  The cutoff angular form equals the angular form on the negative side
statement:
  If \((z,t)\in S^1\times\mathbb R\) with \(t\le0\), then the cutoff angular
  form \(\rho(t)\,d\theta\) equals \(d\theta\) at \((z,t)\).
proof:
  The cutoff satisfies \(\rho(t)=1\) on the nonpositive half-line.
-/
theorem annularCutoffAngularOneForm_eq_angular_of_nonpos
    (v : Circle) (p : Circle × ℝ) (hp : p.2 ≤ 0) :
    (annularCutoffAngularOneForm v).toFun p =
      (annularAngularClosedForm v).1.toFun p := by
  simp [annularCutoffAngularOneForm,
    annularExteriorCutoff_eq_one_of_nonpos hp]

/-! ## Transport to a side-preserving collar -/

/-- The cutoff angular form transported to a full annular collar. -/
noncomputable def exteriorCutoffAngularCollarOneForm
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (v : Circle) :
    SmoothForms (I := SurfaceRealModel) (M := W) ℝ 1 :=
  smoothFormsPullbackDiffeomorph SurfaceRealModel AnnularCylinderModel phi 1
    (annularCutoffAngularOneForm v)

/-- The ambient compact band which contains the derivative defect after
transport to a collar. -/
def exteriorCutoffAngularDefectCore
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ) :
    Set X :=
  (fun q : Circle × ℝ ↦ ((phi.symm q : W) : X)) ''
    annularCutoffAngularCore

/--
%%handwave
name:
  Compactness of the transported cutoff defect band
statement:
  The image in a full annular collar of
  \(S^1\times[\tfrac12,1]\) is a compact subset of the ambient surface.
proof:
  It is the continuous image of the compact cylindrical band under the
  inverse collar chart followed by inclusion into the surface.
-/
theorem exteriorCutoffAngularDefectCore_isCompact
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ) :
    IsCompact (exteriorCutoffAngularDefectCore W phi) := by
  exact annularCutoffAngularCore_isCompact.image
    (continuous_subtype_val.comp phi.symm.continuous)

/--
%%handwave
name:
  The transported defect band lies in the collar
statement:
  The ambient image of the cylindrical transition band is contained in the
  full annular collar.
proof:
  Each point is the ambient image of a point obtained from the inverse collar
  chart.
-/
theorem exteriorCutoffAngularDefectCore_subset_collar
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ) :
    exteriorCutoffAngularDefectCore W phi ⊆ W := by
  rintro _ ⟨q, _hq, rfl⟩
  exact (phi.symm q).2

/--
%%handwave
name:
  The cutoff defect band lies in the incident exterior component
statement:
  Suppose a full annular collar meets a complementary component \(V\) on its
  positive side at a common boundary point.  Then the transported band
  corresponding to \(\tfrac12\le t\le1\) is contained in \(V\).
proof:
  Every point of the band has strictly positive collar coordinate, hence lies
  outside the closed domain.  The collar-side connectedness theorem places
  the entire positive side in the component \(V\).
-/
theorem exteriorCutoffAngularDefectCore_subset_component
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (p : frontier D.carrier) (hpW : (p : X) ∈ W)
    (hpV : (p : X) ∈ frontier V) :
    exteriorCutoffAngularDefectCore W phi ⊆ V := by
  rintro _ ⟨q, hq, rfl⟩
  apply sidePreservingAnnularCollar_exteriorSide_subset_component
    D W phi hexteriorSide V hV p hpW hpV
  refine ⟨(phi.symm q).2, ?_⟩
  apply (hexteriorSide (phi.symm q)).mpr
  rw [phi.apply_symm_apply]
  exact lt_of_lt_of_le (by norm_num) hq.2.1

/--
%%handwave
name:
  The transported cutoff form is closed outside the defect band
statement:
  The exterior derivative of the cutoff angular form pulled back to a full
  annular collar vanishes at every collar point outside the transported
  transition band.
proof:
  Such a point maps outside the cylindrical transition band.  Exterior
  differentiation commutes with pullback by the collar diffeomorphism, and
  the cylindrical cutoff form is closed there.
-/
theorem exteriorCutoffAngularCollarOneForm_derivative_eq_zero_outside
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (v : Circle) (y : W)
    (hy : (y : X) ∉ exteriorCutoffAngularDefectCore W phi) :
    (deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 1
      (exteriorCutoffAngularCollarOneForm W phi v)).toFun y = 0 := by
  have hphi : phi y ∉ annularCutoffAngularCore := by
    intro hycore
    apply hy
    refine ⟨phi y, hycore, ?_⟩
    simp
  rw [exteriorCutoffAngularCollarOneForm,
    deRhamDifferential_smoothFormsPullbackDiffeomorph]
  have hzero :=
    annularCutoffAngularOneForm_derivative_eq_zero_of_not_mem_core
      v (phi y) hphi
  simp only [smoothFormsPullbackDiffeomorph]
  change
    ((deRhamDifferential (I := AnnularCylinderModel)
      (M := Circle × ℝ) (A := ℝ) 1
        (annularCutoffAngularOneForm v)).toFun (phi y)).compContinuousLinearMap _ = 0
  rw [hzero]
  rfl

/-! ## Extension across the exterior component -/

/-- A slightly wider compact band containing the part of the cutoff form on
the nonnegative half-cylinder.  Unlike the derivative core, this includes the
zero slice; that is what makes zero-gluing across the exterior side possible. -/
def annularCutoffAngularSupportCore : Set (Circle × ℝ) :=
  (univ : Set Circle) ×ˢ Icc (0 : ℝ) 1

/--
%%handwave
name:
  Compactness of the angular cutoff support band
statement:
  The wider cylinder band \(S^1\times[0,1]\), containing the nonnegative
  part of the cutoff angular form, is compact.
proof:
  It is a product of the compact circle and a compact interval.
-/
theorem annularCutoffAngularSupportCore_isCompact :
    IsCompact annularCutoffAngularSupportCore := by
  exact isCompact_univ.prod isCompact_Icc

/-- The ambient image of the nonnegative support band. -/
def exteriorCutoffAngularSupportCore
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ) :
    Set X :=
  (fun q : Circle × ℝ ↦ ((phi.symm q : W) : X)) ''
    annularCutoffAngularSupportCore

/--
%%handwave
name:
  Compactness of the transported cutoff support band
statement:
  The image of \(S^1\times[0,1]\) in a full annular collar is compact in the
  ambient surface.
proof:
  It is the continuous image of a compact set under the inverse collar chart
  followed by inclusion.
-/
theorem exteriorCutoffAngularSupportCore_isCompact
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ) :
    IsCompact (exteriorCutoffAngularSupportCore W phi) := by
  exact annularCutoffAngularSupportCore_isCompact.image
    (continuous_subtype_val.comp phi.symm.continuous)

/-- The open complement of the wider support band. -/
def exteriorCutoffAngularSupportExteriorOpen
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ) :
    TopologicalSpace.Opens X :=
  ⟨(exteriorCutoffAngularSupportCore W phi)ᶜ,
    (exteriorCutoffAngularSupportCore_isCompact W phi).isClosed.isOpen_compl⟩

/--
%%handwave
name:
  Vanishing of the cutoff angular form in the far exterior
statement:
  Let an annular collar meet a complementary component on its positive side.
  At a collar point belonging to that component but lying outside the wider
  cutoff band, the pulled-back cutoff angular one-form vanishes.
proof:
  The component condition makes the radial collar coordinate positive.
  Being outside the band \(0\le t\le1\) then forces \(t\ge1\), where the
  cutoff function is zero.
-/
theorem exteriorCutoffAngularCollarOneForm_eq_zero_of_component_and_supportExterior
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (v : Circle) (y : W)
    (hyV : (y : X) ∈ V)
    (hySupport : (y : X) ∉ exteriorCutoffAngularSupportCore W phi) :
    (exteriorCutoffAngularCollarOneForm W phi v).toFun y = 0 := by
  have hyOutside : (y : X) ∉ closure D.carrier := hV.subset hyV
  have hpositive : 0 < (phi y).2 := (hexteriorSide y).mp hyOutside
  have hnotIcc : (phi y).2 ∉ Icc (0 : ℝ) 1 := by
    intro hmem
    apply hySupport
    refine ⟨phi y, ⟨mem_univ _, hmem⟩, ?_⟩
    simp
  have hone : 1 ≤ (phi y).2 := by
    by_contra hnot
    exact hnotIcc ⟨hpositive.le, le_of_not_ge hnot⟩
  simp only [exteriorCutoffAngularCollarOneForm,
    smoothFormsPullbackDiffeomorph]
  change
    ((annularCutoffAngularOneForm v).toFun (phi y)).compContinuousLinearMap _ = 0
  simp [annularCutoffAngularOneForm,
    annularExteriorCutoff_eq_zero_of_one_le hone]
  rfl

/-! The following small wrapper packages the arbitrary-cover gluing theorem
for a union of two opens.  It avoids changing the ambient manifold to the
union subtype by hand. -/

private def twoOpenUnionFamily (U V : TopologicalSpace.Opens X) :
    Bool → TopologicalSpace.Opens X
  | false => U
  | true => V

/--
%%handwave
name:
  Supremum of a two-open family
statement:
  The supremum of the family indexed by two truth values and taking the
  values \(U\) and \(V\) is the open union \(U\cup V\).
proof:
  Membership in the supremum means membership in one of the two indexed
  opens, which is exactly membership in their union.
-/
private theorem iSup_twoOpenUnionFamily
    (U V : TopologicalSpace.Opens X) :
    iSup (twoOpenUnionFamily U V) = U ⊔ V := by
  ext x
  constructor
  · rintro hx
    rcases TopologicalSpace.Opens.mem_iSup.mp hx with ⟨b, hb⟩
    cases b
    · exact Or.inl hb
    · exact Or.inr hb
  · intro hx
    rcases hx with hxU | hxV
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, hxU⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, hxV⟩

def opensDiffeomorphOfMutualLE
    (U V : TopologicalSpace.Opens X) (hUV : U ≤ V) (hVU : V ≤ U) :
    U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ V where
  toEquiv :=
    { toFun := TopologicalSpace.Opens.inclusion hUV
      invFun := TopologicalSpace.Opens.inclusion hVU
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun _ ↦ Subtype.ext rfl }
  contMDiff_toFun := contMDiff_inclusion hUV
  contMDiff_invFun := contMDiff_inclusion hVU

/--
%%handwave
name:
  Derivative of a composite of open inclusions
statement:
  For open subsets \(W\subseteq U\subseteq V\), the derivative of the
  inclusion \(U\hookrightarrow V\), composed with that of
  \(W\hookrightarrow U\), equals the derivative of the direct inclusion
  \(W\hookrightarrow V\).
proof:
  This is the chain rule, since the composite inclusion is definitionally the
  direct inclusion.
-/
private theorem mfderiv_opens_inclusion_comp_inclusion_eq
    (W U V : TopologicalSpace.Opens X) (hWU : W ≤ U) (hUV : U ≤ V)
    (x : W) :
    (mfderiv SurfaceRealModel SurfaceRealModel
        (TopologicalSpace.Opens.inclusion hUV)
        (TopologicalSpace.Opens.inclusion hWU x)).comp
      (mfderiv SurfaceRealModel SurfaceRealModel
        (TopologicalSpace.Opens.inclusion hWU) x) =
    mfderiv SurfaceRealModel SurfaceRealModel
      (TopologicalSpace.Opens.inclusion (hWU.trans hUV)) x := by
  have h := mfderiv_comp
    (I := SurfaceRealModel) (I' := SurfaceRealModel)
    (I'' := SurfaceRealModel) (x := x)
    (g := TopologicalSpace.Opens.inclusion hUV)
    (f := TopologicalSpace.Opens.inclusion hWU)
    ((contMDiff_inclusion (I := SurfaceRealModel) (n := ∞) hUV).contMDiffAt.mdifferentiableAt
      (by simp))
    ((contMDiff_inclusion (I := SurfaceRealModel) (n := ∞) hWU).contMDiffAt.mdifferentiableAt
      (by simp))
  change mfderiv SurfaceRealModel SurfaceRealModel
      (TopologicalSpace.Opens.inclusion (hWU.trans hUV)) x = _ at h
  exact h.symm

/--
%%handwave
name:
  Restriction of an annular pullback to the domain half-collar
statement:
  In a side-preserving collar, restricting the pullback of a smooth annular
  form to the part lying inside the domain agrees with first restricting the
  form to \(S^1\times(-\infty,0)\) and then pulling it back by the restricted
  collar chart.
proof:
  Both constructions evaluate the annular form at the same cylinder point.
  The chain rule identifies the derivative of the full collar chart followed
  by inclusion with that of the restricted chart followed by half-cylinder
  inclusion.
-/
theorem restrict_annularPullback_domain_eq_pullback_negative
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (hside : ∀ y : W, ((y : X) ∈ D.carrier ↔ (phi y).2 < 0))
    {n : ℕ}
    (omega : SmoothForms (I := AnnularCylinderModel)
      (M := Circle × ℝ) ℝ n) :
    let Q := W ⊓ ⟨D.carrier, D.isOpen⟩
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := Q) (V := W) inf_le_left n
        (smoothFormsPullbackDiffeomorph SurfaceRealModel
          AnnularCylinderModel phi n omega) =
      smoothFormsPullbackDiffeomorph SurfaceRealModel AnnularCylinderModel
        (sidePreservingAnnularCollarDomainRestriction D W phi hside) n
        (restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
          negativeAnnularCylinderOpen n omega) := by
  dsimp only
  let Q : TopologicalSpace.Opens X := W ⊓ ⟨D.carrier, D.isOpen⟩
  let psi := sidePreservingAnnularCollarDomainRestriction D W phi hside
  apply DifferentialForm.ext
  intro x
  ext u
  let xW : W := TopologicalSpace.Opens.inclusion inf_le_left x
  let xNeg : negativeAnnularCylinderOpen := psi x
  have hxcoord : (xNeg : Circle × ℝ) = phi xW := by
    rfl
  let f : Q → Circle × ℝ := fun y ↦
    phi (TopologicalSpace.Opens.inclusion inf_le_left y)
  let g : Q → Circle × ℝ := fun y ↦
    ((psi y : negativeAnnularCylinderOpen) : Circle × ℝ)
  have hfg : f = g := by
    funext y
    rfl
  have hfcomp :
      mfderiv SurfaceRealModel AnnularCylinderModel f x =
        (mfderiv SurfaceRealModel AnnularCylinderModel phi xW).comp
          (mfderiv SurfaceRealModel SurfaceRealModel
            (TopologicalSpace.Opens.inclusion inf_le_left) x) := by
    exact mfderiv_comp x
      (phi.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      ((contMDiff_inclusion (I := SurfaceRealModel) (n := ∞)
        inf_le_left).contMDiffAt.mdifferentiableAt (by simp))
  have hgcomp :
      mfderiv SurfaceRealModel AnnularCylinderModel g x =
        (mfderiv AnnularCylinderModel AnnularCylinderModel
          (fun z : negativeAnnularCylinderOpen ↦ (z : Circle × ℝ)) xNeg).comp
          (mfderiv SurfaceRealModel AnnularCylinderModel psi x) := by
    exact mfderiv_comp x
      ((contMDiff_subtype_val (I := AnnularCylinderModel)
        (n := ∞)).contMDiffAt.mdifferentiableAt (by simp))
      (psi.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have hderiv :
      (mfderiv SurfaceRealModel AnnularCylinderModel phi xW).comp
          (mfderiv SurfaceRealModel SurfaceRealModel
            (TopologicalSpace.Opens.inclusion inf_le_left) x) =
        (mfderiv AnnularCylinderModel AnnularCylinderModel
          (fun z : negativeAnnularCylinderOpen ↦ (z : Circle × ℝ)) xNeg).comp
          (mfderiv SurfaceRealModel AnnularCylinderModel psi x) := by
    rw [← hfcomp, ← hgcomp, hfg]
  simp only [restrictSmoothFormsOfLE, smoothFormsPullbackDiffeomorph,
    restrictSmoothFormsToOpen]
  change
    omega.toFun (phi xW)
        (((mfderiv SurfaceRealModel AnnularCylinderModel phi xW).comp
          (mfderiv SurfaceRealModel SurfaceRealModel
            (TopologicalSpace.Opens.inclusion inf_le_left) x)) ∘ u) =
      omega.toFun (xNeg : Circle × ℝ)
        (((mfderiv AnnularCylinderModel AnnularCylinderModel
          (fun z : negativeAnnularCylinderOpen ↦ (z : Circle × ℝ)) xNeg).comp
          (mfderiv SurfaceRealModel AnnularCylinderModel psi x)) ∘ u)
  rw [hxcoord, hderiv]
  rfl

/--
%%handwave
name:
  The cutoff form restricts to the angular form on the domain half-collar
statement:
  On the domain side of a side-preserving annular collar, the cutoff angular
  one-form equals the pullback of the normalized angular form restricted to
  the negative half-cylinder.
proof:
  Domain points have collar coordinate \(t<0\), where the cutoff is identically
  one.  The general restriction-pullback identity then identifies the two
  forms, including their tangent maps.
-/
theorem restrict_exteriorCutoffAngularCollarOneForm_domain_eq_pullback_negative
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (hside : ∀ y : W, ((y : X) ∈ D.carrier ↔ (phi y).2 < 0))
    (v : Circle) :
    let Q := W ⊓ ⟨D.carrier, D.isOpen⟩
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := Q) (V := W) inf_le_left 1
        (exteriorCutoffAngularCollarOneForm W phi v) =
      smoothFormsPullbackDiffeomorph SurfaceRealModel AnnularCylinderModel
        (sidePreservingAnnularCollarDomainRestriction D W phi hside) 1
        (restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
          negativeAnnularCylinderOpen 1 (annularAngularClosedForm v).1) := by
  dsimp only
  let Q : TopologicalSpace.Opens X := W ⊓ ⟨D.carrier, D.isOpen⟩
  let psi := sidePreservingAnnularCollarDomainRestriction D W phi hside
  apply DifferentialForm.ext
  intro x
  ext u
  let xW : W := TopologicalSpace.Opens.inclusion inf_le_left x
  let xNeg : negativeAnnularCylinderOpen := psi x
  have hxcoord : (xNeg : Circle × ℝ) = phi xW := by
    rfl
  have hxnegative : (phi xW).2 ≤ 0 :=
    ((hside xW).mp x.2.2).le
  have hform := annularCutoffAngularOneForm_eq_angular_of_nonpos
    v (phi xW) hxnegative
  let f : Q → Circle × ℝ := fun y ↦
    phi (TopologicalSpace.Opens.inclusion inf_le_left y)
  let g : Q → Circle × ℝ := fun y ↦
    ((psi y : negativeAnnularCylinderOpen) : Circle × ℝ)
  have hfg : f = g := by
    funext y
    rfl
  have hfcomp :
      mfderiv SurfaceRealModel AnnularCylinderModel f x =
        (mfderiv SurfaceRealModel AnnularCylinderModel phi xW).comp
          (mfderiv SurfaceRealModel SurfaceRealModel
            (TopologicalSpace.Opens.inclusion inf_le_left) x) := by
    have h := mfderiv_comp
      (I := SurfaceRealModel) (I' := SurfaceRealModel)
      (I'' := AnnularCylinderModel) (x := x)
      (g := phi) (f := TopologicalSpace.Opens.inclusion inf_le_left)
      (phi.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      ((contMDiff_inclusion (I := SurfaceRealModel) (n := ∞) inf_le_left).contMDiffAt.mdifferentiableAt
        (by simp))
    exact h
  have hgcomp :
      mfderiv SurfaceRealModel AnnularCylinderModel g x =
        (mfderiv AnnularCylinderModel AnnularCylinderModel
          (fun z : negativeAnnularCylinderOpen ↦ (z : Circle × ℝ)) xNeg).comp
          (mfderiv SurfaceRealModel AnnularCylinderModel psi x) := by
    have h := mfderiv_comp
      (I := SurfaceRealModel) (I' := AnnularCylinderModel)
      (I'' := AnnularCylinderModel) (x := x)
      (g := fun z : negativeAnnularCylinderOpen ↦ (z : Circle × ℝ))
      (f := psi)
      ((contMDiff_subtype_val (I := AnnularCylinderModel) (n := ∞)).contMDiffAt.mdifferentiableAt
        (by simp))
      (psi.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    exact h
  have hderiv :
      (mfderiv SurfaceRealModel AnnularCylinderModel phi xW).comp
          (mfderiv SurfaceRealModel SurfaceRealModel
            (TopologicalSpace.Opens.inclusion inf_le_left) x) =
        (mfderiv AnnularCylinderModel AnnularCylinderModel
          (fun z : negativeAnnularCylinderOpen ↦ (z : Circle × ℝ)) xNeg).comp
          (mfderiv SurfaceRealModel AnnularCylinderModel psi x) := by
    rw [← hfcomp, ← hgcomp, hfg]
  simp only [restrictSmoothFormsOfLE, exteriorCutoffAngularCollarOneForm,
    smoothFormsPullbackDiffeomorph, restrictSmoothFormsToOpen]
  change
    (annularCutoffAngularOneForm v).toFun (phi xW)
        (((mfderiv SurfaceRealModel AnnularCylinderModel phi xW).comp
          (mfderiv SurfaceRealModel SurfaceRealModel
            (TopologicalSpace.Opens.inclusion inf_le_left) x)) ∘ u) =
      (annularAngularClosedForm v).1.toFun (xNeg : Circle × ℝ)
        (((mfderiv AnnularCylinderModel AnnularCylinderModel
          (fun z : negativeAnnularCylinderOpen ↦ (z : Circle × ℝ)) xNeg).comp
          (mfderiv SurfaceRealModel AnnularCylinderModel psi x)) ∘ u)
  rw [hform, hxcoord, hderiv]
  rfl

/--
%%handwave
name:
  A side-preserving half-collar has angular period minus one
statement:
  Let \(Q\) be the part of a side-preserving annular collar lying inside the
  domain.  The pullback to \(Q\) of the normalized angular form on the
  negative half-cylinder has a smooth singular one-cycle \(c\) satisfying
  \[
    \partial c=0,\qquad \int_c\omega=-1.
  \]
proof:
  Transport the standard negative annular cycle of angular period \(-1\)
  through the collar diffeomorphism.  Naturality of the boundary and of
  integration under diffeomorphisms gives both identities.
-/
theorem exists_sidePreservingAnnularCollarDomainCycle_angular_period_eq_neg_one
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (hside : ∀ y : W, ((y : X) ∈ D.carrier ↔ (phi y).2 < 0))
    (v : Circle) :
    let Q := W ⊓ ⟨D.carrier, D.isOpen⟩
    let psi := sidePreservingAnnularCollarDomainRestriction D W phi hside
    ∃ c : SingularChain (I := SurfaceRealModel) (M := Q) 1 ∞,
      boundary (I := SurfaceRealModel) c = 0 ∧
        integrateSmoothChain (I := SurfaceRealModel)
          (smoothFormsPullbackDiffeomorph SurfaceRealModel
            AnnularCylinderModel psi 1
            (restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
              negativeAnnularCylinderOpen 1
              (annularAngularClosedForm v).1)) c = -1 := by
  dsimp only
  let Q : TopologicalSpace.Opens X := W ⊓ ⟨D.carrier, D.isOpen⟩
  let psi := sidePreservingAnnularCollarDomainRestriction D W phi hside
  let beta : SmoothForms (I := AnnularCylinderModel)
      (M := negativeAnnularCylinderOpen) ℝ 1 :=
    restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
      negativeAnnularCylinderOpen 1 (annularAngularClosedForm v).1
  rcases exists_negativeAnnularCycle_angular_period_eq_neg_one v with
    ⟨cNeg, hcycleNeg, hperiodNeg⟩
  let cQ : SingularChain (I := SurfaceRealModel) (M := Q) 1 ∞ :=
    SingularChain.postcompose (I := AnnularCylinderModel)
      psi.symm.toContMDiffMap cNeg
  refine ⟨cQ, ?_, ?_⟩
  · calc
      boundary (I := SurfaceRealModel) cQ =
          SingularChain.postcompose (I := AnnularCylinderModel)
            psi.symm.toContMDiffMap
              (boundary (I := AnnularCylinderModel) cNeg) := by
                exact (SingularChain.postcompose_boundary
                  (I := AnnularCylinderModel) psi.symm.toContMDiffMap cNeg).symm
      _ = 0 := by rw [hcycleNeg]; simp
  · have htransport := integrateSmoothChain_diffeomorph
        AnnularCylinderModel SurfaceRealModel psi.symm
        (smoothFormsPullbackDiffeomorph SurfaceRealModel
          AnnularCylinderModel psi 1 beta) cNeg
    have hpullback :
        smoothFormsPullbackDiffeomorph AnnularCylinderModel
            SurfaceRealModel psi.symm 1
            (smoothFormsPullbackDiffeomorph SurfaceRealModel
              AnnularCylinderModel psi 1 beta) = beta :=
      smoothFormsPullbackDiffeomorph_symm_comp
        SurfaceRealModel AnnularCylinderModel psi beta
    rw [hpullback] at htransport
    simpa [cQ, beta] using htransport.trans hperiodNeg

noncomputable def smoothFormsTransportOpenMutualLE
    (U V : TopologicalSpace.Opens X) (hUV : U ≤ V) (hVU : V ≤ U)
    {n : ℕ} (alpha : SmoothForms (I := SurfaceRealModel) (M := U) ℝ n) :
    SmoothForms (I := SurfaceRealModel) (M := V) ℝ n :=
  smoothFormsPullbackDiffeomorph SurfaceRealModel SurfaceRealModel
    (opensDiffeomorphOfMutualLE V U hVU hUV) n alpha

/--
%%handwave
name:
  Restriction after identifying equal open sets
statement:
  Suppose \(U\) and \(V\) are mutually contained open subsets of a manifold,
  and \(W\subseteq U,V\).  Transporting a smooth differential form from
  \(U\) to \(V\) through the canonical identification and then restricting
  to \(W\) agrees with restricting the original form directly from \(U\).
proof:
  Evaluate both forms at a point of \(W\).  The two underlying points agree,
  and the chain rule identifies the composite derivatives of the open-set
  inclusions.
-/
theorem restrictSmoothFormsOfLE_transportOpenMutualLE
    (W U V : TopologicalSpace.Opens X)
    (hWU : W ≤ U) (hWV : W ≤ V) (hUV : U ≤ V) (hVU : V ≤ U)
    {n : ℕ} (alpha : SmoothForms (I := SurfaceRealModel) (M := U) ℝ n) :
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := W) (V := V) hWV n
        (smoothFormsTransportOpenMutualLE U V hUV hVU alpha) =
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := W) (V := U) hWU n alpha := by
  apply DifferentialForm.ext
  intro x
  ext w
  let xV : V := TopologicalSpace.Opens.inclusion hWV x
  let xU : U := TopologicalSpace.Opens.inclusion hWU x
  have hx : TopologicalSpace.Opens.inclusion hVU xV = xU := Subtype.ext rfl
  have hderivV := mfderiv_opens_inclusion_comp_inclusion_eq
    W V U hWV hVU x
  have hproof : hWV.trans hVU = hWU := Subsingleton.elim _ _
  rw [hproof] at hderivV
  simp only [smoothFormsTransportOpenMutualLE,
    smoothFormsPullbackDiffeomorph, restrictSmoothFormsOfLE]
  change alpha.toFun (TopologicalSpace.Opens.inclusion hVU xV)
      (((mfderiv SurfaceRealModel SurfaceRealModel
          (TopologicalSpace.Opens.inclusion hVU) xV).comp
        (mfderiv SurfaceRealModel SurfaceRealModel
          (TopologicalSpace.Opens.inclusion hWV) x)) ∘ w) =
    alpha.toFun xU
      ((mfderiv SurfaceRealModel SurfaceRealModel
        (TopologicalSpace.Opens.inclusion hWU) x) ∘ w)
  rw [hx, hderivV]

/--
%%handwave
name:
  Gluing a smooth form to zero across two open sets
statement:
  Let \(U,V\) be open and let \(\alpha\) be a smooth differential form on
  \(U\) that vanishes at every point of \(U\cap V\).  There is a smooth form
  \(\gamma\) on \(U\cup V\) such that
  \(\gamma|_U=\alpha\) and \(\gamma|_V=0\).
proof:
  The forms \(\alpha\) and \(0\) agree on the overlap, so the sheaf gluing
  theorem produces a form on the supremum of the two opens.  Transport it
  through the canonical identification of that supremum with \(U\cup V\).
-/
private theorem exists_smoothFormsTwoOpenUnionZeroGlue
    (U V : TopologicalSpace.Opens X) {n : ℕ}
    (alpha : SmoothForms (I := SurfaceRealModel) (M := U) ℝ n)
    (hzero : ∀ x : U, (x : X) ∈ V → alpha.toFun x = 0) :
    ∃ gamma : SmoothForms (I := SurfaceRealModel)
        (M := (U ⊔ V : TopologicalSpace.Opens X)) ℝ n,
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := U) (V := U ⊔ V) le_sup_left n gamma = alpha ∧
        restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := V) (V := U ⊔ V) le_sup_right n gamma = 0 := by
  let F := twoOpenUnionFamily U V
  let forms : ∀ b, SmoothForms (I := SurfaceRealModel) (M := F b) ℝ n
    | false => alpha
    | true => 0
  have hcompat : ∀ i j,
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := F i ⊓ F j) (V := F i) inf_le_left n (forms i) =
        restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := F i ⊓ F j) (V := F j) inf_le_right n (forms j) := by
    intro i j
    cases i <;> cases j
    · rfl
    · apply DifferentialForm.ext
      intro x
      ext w
      let xU : U := TopologicalSpace.Opens.inclusion inf_le_left x
      have hxzero : alpha.toFun xU = 0 := hzero xU x.2.2
      simp only [F, forms, twoOpenUnionFamily, restrictSmoothFormsOfLE]
      change alpha.toFun xU (_ ∘ w) = 0
      rw [hxzero]
      rfl
    · apply DifferentialForm.ext
      intro x
      ext w
      let xU : U := TopologicalSpace.Opens.inclusion inf_le_right x
      have hxzero : alpha.toFun xU = 0 := hzero xU x.2.1
      simp only [F, forms, twoOpenUnionFamily, restrictSmoothFormsOfLE]
      change 0 = alpha.toFun xU (_ ∘ w)
      rw [hxzero]
      rfl
    · rfl
  rcases exists_smoothForms_iSup_gluing
      (M := X) SurfaceRealModel n F forms hcompat with ⟨gammaSup, hgamma⟩
  have hsup : iSup F = U ⊔ V := iSup_twoOpenUnionFamily U V
  let gamma := smoothFormsTransportOpenMutualLE
    (iSup F) (U ⊔ V) hsup.le hsup.ge gammaSup
  refine ⟨gamma, ?_, ?_⟩
  · rw [restrictSmoothFormsOfLE_transportOpenMutualLE
      U (iSup F) (U ⊔ V) (le_iSup F false) le_sup_left hsup.le hsup.ge]
    simpa only [F, forms, twoOpenUnionFamily] using hgamma false
  · rw [restrictSmoothFormsOfLE_transportOpenMutualLE
      V (iSup F) (U ⊔ V) (le_iSup F true) le_sup_right hsup.le hsup.ge]
    simpa only [F, forms, twoOpenUnionFamily] using hgamma true

/--
%%handwave
name:
  The cutoff support band lies in the collar
statement:
  The image in the surface of the compact annular band supporting the cutoff
  angular form is contained in the full collar.
proof:
  Every point of the band is, by construction, the image under the inverse
  collar chart of a cylinder point.
-/
theorem exteriorCutoffAngularSupportCore_subset_collar
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ) :
    exteriorCutoffAngularSupportCore W phi ⊆ W := by
  rintro _ ⟨q, _hq, rfl⟩
  exact (phi.symm q).2

/-- The part of the exterior component lying beyond the wider cutoff band. -/
def exteriorCutoffAngularFarExteriorOpen
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (V : Set X) (hVopen : IsOpen V) : TopologicalSpace.Opens X :=
  ⟨V, hVopen⟩ ⊓ exteriorCutoffAngularSupportExteriorOpen W phi

/--
%%handwave
name:
  The collar and far exterior cover the collar-component union
statement:
  If the far exterior is the part of an exterior component outside the
  cutoff support band, then
  \[
    W\cup V_{\mathrm{far}}=W\cup V.
  \]
proof:
  One inclusion is immediate.  For the reverse inclusion, a point of \(V\)
  is either outside the support band, hence in the far exterior, or inside
  the band, which is contained in the collar \(W\).
-/
theorem collar_sup_farExteriorOpen
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (V : Set X) (hVopen : IsOpen V) :
    W ⊔ exteriorCutoffAngularFarExteriorOpen W phi V hVopen =
      exteriorComponentCollarUnion W V hVopen := by
  ext x
  constructor
  · rintro (hxW | ⟨hxV, _hxFar⟩)
    · exact Or.inl hxW
    · exact Or.inr hxV
  · rintro (hxW | hxV)
    · exact Or.inl hxW
    · by_cases hxCore : x ∈ exteriorCutoffAngularSupportCore W phi
      · exact Or.inl (exteriorCutoffAngularSupportCore_subset_collar W phi hxCore)
      · exact Or.inr ⟨hxV, hxCore⟩

/--
%%handwave
name:
  Smooth extension of the cutoff angular form to an exterior component
statement:
  Let an annular collar meet a complementary component \(V\) on its positive
  side.  The cutoff angular one-form on the collar extends to a smooth
  one-form on \(W\cup V\) which vanishes on the part of \(V\) beyond the
  cutoff support band.
proof:
  On the overlap of the collar with the far exterior, positivity of the
  collar coordinate forces the cutoff form to vanish.  Glue it there to the
  zero form and identify the resulting union with \(W\cup V\).
-/
theorem exists_exteriorCutoffAngularExtension
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (v : Circle) :
    let hVopen := hV.isOpen_of_isOpen isClosed_closure.isOpen_compl
    let S := exteriorComponentCollarUnion W V hVopen
    let Z := exteriorCutoffAngularFarExteriorOpen W phi V hVopen
    ∃ alpha : SmoothForms (I := SurfaceRealModel) (M := S) ℝ 1,
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := W) (V := S) le_sup_left 1 alpha =
        exteriorCutoffAngularCollarOneForm W phi v ∧
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := Z) (V := S) (inf_le_left.trans le_sup_right) 1 alpha = 0 := by
  dsimp only
  let hVopen := hV.isOpen_of_isOpen isClosed_closure.isOpen_compl
  let S := exteriorComponentCollarUnion W V hVopen
  let Z := exteriorCutoffAngularFarExteriorOpen W phi V hVopen
  have hzero : ∀ y : W, (y : X) ∈ Z →
      (exteriorCutoffAngularCollarOneForm W phi v).toFun y = 0 := by
    intro y hy
    exact exteriorCutoffAngularCollarOneForm_eq_zero_of_component_and_supportExterior
      D W phi hexteriorSide V hV v y hy.1 hy.2
  rcases exists_smoothFormsTwoOpenUnionZeroGlue W Z
      (exteriorCutoffAngularCollarOneForm W phi v) hzero with
    ⟨alphaUnion, halphaW, halphaZ⟩
  have hUnion : W ⊔ Z = S := by
    exact collar_sup_farExteriorOpen W phi V hVopen
  let alpha : SmoothForms (I := SurfaceRealModel) (M := S) ℝ 1 :=
    smoothFormsTransportOpenMutualLE (W ⊔ Z) S
      hUnion.le hUnion.ge alphaUnion
  refine ⟨alpha, ?_, ?_⟩
  · rw [restrictSmoothFormsOfLE_transportOpenMutualLE
      W (W ⊔ Z) S le_sup_left le_sup_left hUnion.le hUnion.ge]
    exact halphaW
  · rw [restrictSmoothFormsOfLE_transportOpenMutualLE
      Z (W ⊔ Z) S le_sup_right (inf_le_left.trans le_sup_right)
        hUnion.le hUnion.ge]
    exact halphaZ

/--
%%handwave
name:
  Pointwise vanishing detected by restriction
statement:
  Let \(W\subseteq V\) be open subsets and let \(\omega\) be a smooth
  differential form on \(V\).  If its restriction equals a form \(\beta\) on
  \(W\) and \(\beta_x=0\), then \(\omega_x=0\) at the corresponding point
  of \(V\).
proof:
  Restriction composes the multilinear form with the derivative of the open
  inclusion.  That derivative is surjective, so vanishing of the composite
  forces the original multilinear form to vanish.
-/
private theorem smoothForms_toFun_eq_zero_of_restriction_eq_local
    (W V : TopologicalSpace.Opens X) (hWV : W ≤ V) {n : ℕ}
    (omega : SmoothForms (I := SurfaceRealModel) (M := V) ℝ n)
    (beta : SmoothForms (I := SurfaceRealModel) (M := W) ℝ n)
    (hrestrict :
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := W) (V := V) hWV n omega = beta)
    (x : W) (hbeta : beta.toFun x = 0) :
    omega.toFun (TopologicalSpace.Opens.inclusion hWV x) = 0 := by
  have hpoint := congrArg
    (fun eta : SmoothForms (I := SurfaceRealModel) (M := W) ℝ n ↦ eta.toFun x)
    hrestrict
  change
    (omega.toFun (TopologicalSpace.Opens.inclusion hWV x)).compContinuousLinearMap
        (mfderiv SurfaceRealModel SurfaceRealModel
          (TopologicalSpace.Opens.inclusion hWV) x) = beta.toFun x at hpoint
  rw [hbeta] at hpoint
  exact continuousAlternatingMap_compContinuousLinearMap_injective
    (mfderiv SurfaceRealModel SurfaceRealModel
      (TopologicalSpace.Opens.inclusion hWV) x)
    (mfderiv_opens_inclusion_isInvertible
      (I := SurfaceRealModel) W V hWV x).surjective hpoint

/--
%%handwave
name:
  Transitivity of restriction for smooth forms
statement:
  For open subsets \(W\subseteq V\subseteq U\), restricting a smooth
  differential form directly from \(U\) to \(W\) agrees with first
  restricting to \(V\) and then to \(W\).
proof:
  Evaluate at a point of \(W\) and use the chain rule for the two open-set
  inclusions.
-/
theorem restrictSmoothFormsOfLE_trans
    (W V U : TopologicalSpace.Opens X) (hWV : W ≤ V) (hVU : V ≤ U)
    {n : ℕ} (omega : SmoothForms (I := SurfaceRealModel) (M := U) ℝ n) :
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := W) (V := U) (hWV.trans hVU) n omega =
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := W) (V := V) hWV n
        (restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := V) (V := U) hVU n omega) := by
  apply DifferentialForm.ext
  intro x
  ext w
  let xV : V := TopologicalSpace.Opens.inclusion hWV x
  let xU : U := TopologicalSpace.Opens.inclusion (hWV.trans hVU) x
  have hx : TopologicalSpace.Opens.inclusion hVU xV = xU := Subtype.ext rfl
  have hderiv := mfderiv_opens_inclusion_comp_inclusion_eq W V U hWV hVU x
  simp only [restrictSmoothFormsOfLE]
  change omega.toFun xU
      ((mfderiv SurfaceRealModel SurfaceRealModel
        (TopologicalSpace.Opens.inclusion (hWV.trans hVU)) x) ∘ w) =
    omega.toFun (TopologicalSpace.Opens.inclusion hVU xV)
      (((mfderiv SurfaceRealModel SurfaceRealModel
          (TopologicalSpace.Opens.inclusion hVU) xV).comp
        (mfderiv SurfaceRealModel SurfaceRealModel
          (TopologicalSpace.Opens.inclusion hWV) x)) ∘ w)
  rw [hx, hderiv]

/--
%%handwave
name:
  Transitivity of restriction in de Rham cohomology
statement:
  For open subsets \(W\subseteq V\subseteq U\), restriction of a de Rham
  class from \(U\) directly to \(W\) equals the composite of its restrictions
  from \(U\) to \(V\) and from \(V\) to \(W\).
proof:
  Represent the class by a closed form and apply transitivity of restriction
  for smooth forms before passing to the quotient by exact forms.
-/
theorem deRhamCohomologyRestrictionOfLE_trans
    (W V U : TopologicalSpace.Opens X) (hWV : W ≤ V) (hVU : V ≤ U)
    (n : ℕ)
    (alpha : DeRhamCohomology (I := SurfaceRealModel)
      (M := U) (A := ℝ) n) :
    deRhamCohomologyRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
        (hWV.trans hVU) n alpha =
      deRhamCohomologyRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
        hWV n
        (deRhamCohomologyRestrictionOfLE
          (I := SurfaceRealModel) (A := ℝ) hVU n alpha) := by
  refine Quotient.inductionOn' alpha ?_
  intro omega
  apply congrArg
    (DeRhamExactClosedForms (I := SurfaceRealModel)
      (M := W) (A := ℝ) n).mkQ
  apply Subtype.ext
  exact restrictSmoothFormsOfLE_trans W V U hWV hVU omega.1

/--
%%handwave
name:
  The exterior extension is closed outside the cutoff defect band
statement:
  Let \(\alpha\) be a smooth extension to \(W\cup V\) of the cutoff angular
  form on the collar which vanishes far out in \(V\).  Then
  \(d\alpha=0\) at every point outside the compact transition band of the
  cutoff.
proof:
  The collar and far exterior cover \(W\cup V\).  On the collar, naturality
  of \(d\) reduces the assertion to the corresponding support statement for
  the cutoff angular form; on the far exterior, \(\alpha\) restricts to zero,
  so its derivative does also.
-/
theorem deRhamDifferential_exteriorCutoffAngularExtension_eq_zero_outside_defectCore
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (v : Circle)
    (alpha : SmoothForms (I := SurfaceRealModel)
      (M := exteriorComponentCollarUnion W V
        (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl)) ℝ 1)
    (halphaW :
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := W)
          (V := exteriorComponentCollarUnion W V
            (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl))
          le_sup_left 1 alpha = exteriorCutoffAngularCollarOneForm W phi v)
    (halphaZ :
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := exteriorCutoffAngularFarExteriorOpen W phi V
            (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl))
          (V := exteriorComponentCollarUnion W V
            (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl))
          (inf_le_left.trans le_sup_right) 1 alpha = 0)
    (x : exteriorComponentCollarUnion W V
      (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl))
    (hx : (x : X) ∉ exteriorCutoffAngularDefectCore W phi) :
    (deRhamDifferential (I := SurfaceRealModel)
      (M := exteriorComponentCollarUnion W V
        (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl))
      (A := ℝ) 1 alpha).toFun x = 0 := by
  let hVopen := hV.isOpen_of_isOpen isClosed_closure.isOpen_compl
  let S := exteriorComponentCollarUnion W V hVopen
  let Z := exteriorCutoffAngularFarExteriorOpen W phi V hVopen
  have hUnion : W ⊔ Z = S := collar_sup_farExteriorOpen W phi V hVopen
  have hxCover : (x : X) ∈ W ∨ (x : X) ∈ Z := by
    have hx' : (x : X) ∈ W ⊔ Z := by
      rw [hUnion]
      exact x.2
    exact hx'
  rcases hxCover with hxW | hxZ
  · let xW : W := ⟨(x : X), hxW⟩
    have hlocal :
        (deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 1
          (exteriorCutoffAngularCollarOneForm W phi v)).toFun xW = 0 :=
      exteriorCutoffAngularCollarOneForm_derivative_eq_zero_outside
        W phi v xW hx
    have hrestrict :
        restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
            (W := W) (V := S) le_sup_left 2
            (deRhamDifferential (I := SurfaceRealModel) (M := S) (A := ℝ) 1
              alpha) =
          deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 1
            (exteriorCutoffAngularCollarOneForm W phi v) := by
      calc
        _ = deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 1
            (restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
              (W := W) (V := S) le_sup_left 1 alpha) :=
          (deRhamDifferential_restrictSmoothFormsOfLE
            (I := SurfaceRealModel) (A := ℝ) le_sup_left alpha).symm
        _ = _ := congrArg
          (deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 1)
          halphaW
    have hzero := smoothForms_toFun_eq_zero_of_restriction_eq_local
      W S le_sup_left
      (deRhamDifferential (I := SurfaceRealModel) (M := S) (A := ℝ) 1 alpha)
      (deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 1
        (exteriorCutoffAngularCollarOneForm W phi v))
      hrestrict xW hlocal
    simpa [xW] using hzero
  · let xZ : Z := ⟨(x : X), hxZ⟩
    have hrestrict :
        restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
            (W := Z) (V := S) (inf_le_left.trans le_sup_right) 2
            (deRhamDifferential (I := SurfaceRealModel) (M := S) (A := ℝ) 1
              alpha) = 0 := by
      calc
        _ = deRhamDifferential (I := SurfaceRealModel) (M := Z) (A := ℝ) 1
            (restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
              (W := Z) (V := S) (inf_le_left.trans le_sup_right) 1 alpha) :=
          (deRhamDifferential_restrictSmoothFormsOfLE
            (I := SurfaceRealModel) (A := ℝ)
            (inf_le_left.trans le_sup_right) alpha).symm
        _ = deRhamDifferential (I := SurfaceRealModel) (M := Z) (A := ℝ) 1 0 :=
          congrArg (deRhamDifferential (I := SurfaceRealModel) (M := Z) (A := ℝ) 1)
            halphaZ
        _ = 0 := LinearMap.map_zero _
    have hzero := smoothForms_toFun_eq_zero_of_restriction_eq_local
      Z S (inf_le_left.trans le_sup_right)
      (deRhamDifferential (I := SurfaceRealModel) (M := S) (A := ℝ) 1 alpha)
      0 hrestrict xZ rfl
    simpa [xZ] using hzero

/--
%%handwave
name:
  Closed angular extension into an exterior component
statement:
  Let a full collar \(W\cong S^1\times\mathbb R\) meet an exterior component
  \(V\) along its positive side.  For every normalized angular form on the
  cylinder, there is a closed one-form \(\eta\) on \(W\cup V\) whose
  restriction to the domain half-collar agrees with the pulled-back angular
  form.
proof:
  Cut off the angular form toward the positive end; its failure to be closed
  is a compactly supported two-form lying in \(V\).  Transport this defect to
  infinity to find a one-form \(\theta\), supported in \(V\), with
  \(d\theta\) equal to the defect.  Subtracting \(\theta\) produces a closed
  form and does not change the form on the domain half-collar.
-/
theorem IsExteriorComponent.exists_closed_exteriorAngularExtension
    (E : SmoothRelativelyCompactExhaustion X)
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hVext : IsExteriorComponent (closure D.carrier) V)
    (p : frontier D.carrier) (hpW : (p : X) ∈ W)
    (hpV : (p : X) ∈ frontier V)
    (v : Circle) :
    let hVopen := hVext.isComponentOf.isOpen_of_isOpen
      isClosed_closure.isOpen_compl
    let S := exteriorComponentCollarUnion W V hVopen
    let Q := W ⊓ ⟨D.carrier, D.isOpen⟩
    ∃ eta : DeRhamClosedForms (I := SurfaceRealModel) (M := S) (A := ℝ) 1,
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := Q) (V := S) (inf_le_left.trans le_sup_left) 1 eta.1 =
        restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := Q) (V := W) inf_le_left 1
          (exteriorCutoffAngularCollarOneForm W phi v) := by
  dsimp only
  let hV := hVext.isComponentOf
  let hVopen := hV.isOpen_of_isOpen isClosed_closure.isOpen_compl
  let S := exteriorComponentCollarUnion W V hVopen
  let Z := exteriorCutoffAngularFarExteriorOpen W phi V hVopen
  let Q := W ⊓ ⟨D.carrier, D.isOpen⟩
  rcases exists_exteriorCutoffAngularExtension
      D W phi hexteriorSide V hV v with ⟨alpha, halphaW, halphaZ⟩
  let C := exteriorCutoffAngularDefectCore W phi
  have hCcompact : IsCompact C := exteriorCutoffAngularDefectCore_isCompact W phi
  have hCV : C ⊆ V :=
    exteriorCutoffAngularDefectCore_subset_component
      D W phi hexteriorSide V hV p hpW hpV
  have hCS : C ⊆ S := by
    intro x hx
    exact Or.inl (exteriorCutoffAngularDefectCore_subset_collar W phi hx)
  let KS : Set S := smoothFormCompactCoreInOpen S C
  have hKScompact : IsCompact KS :=
    smoothFormCompactCoreInOpen_isCompact S C hCcompact hCS
  have hdalphaZero : ∀ x : S, x ∉ KS →
      (deRhamDifferential (I := SurfaceRealModel) (M := S) (A := ℝ) 1 alpha).toFun x = 0 := by
    intro x hxKS
    apply deRhamDifferential_exteriorCutoffAngularExtension_eq_zero_outside_defectCore
      D W phi V hV v alpha halphaW halphaZ x
    exact hxKS
  let omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2 :=
    smoothFormCompactZeroExtension SurfaceRealModel S KS hKScompact
      (deRhamDifferential (I := SurfaceRealModel) (M := S) (A := ℝ) 1 alpha)
      hdalphaZero
  have homegaZero : ∀ x : X, x ∉ C → omega.toFun x = 0 := by
    intro x hxC
    apply smoothFormCompactZeroExtension_toFun_eq_zero_of_not_mem_core
      SurfaceRealModel S KS hKScompact
      (deRhamDifferential (I := SurfaceRealModel) (M := S) (A := ℝ) 1 alpha)
      hdalphaZero x
    rw [smoothFormCompactCore_coreInOpen S C hCS]
    exact hxC
  rcases hVext.nonempty with ⟨y₀, hy₀V⟩
  let Vopen : TopologicalSpace.Opens X :=
    ⟨V, hV.isOpen_of_isOpen isClosed_closure.isOpen_compl⟩
  rcases exists_complexPlanarChart_subordinate Vopen y₀ hy₀V with
    ⟨T, hy₀T, hTV, hphiT⟩
  let yT : T := ⟨y₀, hy₀T⟩
  rcases hVext.exists_compactSupport_consolidation_in_open
      D.compact_closure hCcompact hCV T hTV yT omega homegaZero with
    ⟨eta₀, beta, KT, hKTcompact, heta₀, heta₀Support, hbeta⟩
  rcases hVext.exists_primitive_of_compactSupport_in_coordinateChart_with_support
      E D.compact_closure T hTV yT (Classical.choice hphiT)
        KT hKTcompact beta hbeta with
    ⟨thetaTail, hthetaTail, hthetaTailSupport⟩
  let theta := eta₀ + thetaTail
  have htheta :
      deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1 theta =
        omega := by
    change deRhamDifferential
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1 (eta₀ + thetaTail) = omega
    rw [map_add, heta₀, hthetaTail]
    abel
  have hthetaSupport : ∀ y : X, y ∉ V → theta.toFun y = 0 := by
    intro y hyV
    change eta₀.toFun y + thetaTail.toFun y = 0
    rw [heta₀Support y hyV, hthetaTailSupport y hyV]
    exact zero_add 0
  let thetaS : SmoothForms (I := SurfaceRealModel) (M := S) ℝ 1 :=
    restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) S 1 theta
  let etaForm : SmoothForms (I := SurfaceRealModel) (M := S) ℝ 1 :=
    alpha - thetaS
  have hthetaS :
      deRhamDifferential (I := SurfaceRealModel) (M := S) (A := ℝ) 1 thetaS =
        deRhamDifferential (I := SurfaceRealModel) (M := S) (A := ℝ) 1 alpha := by
    calc
      _ = restrictSmoothFormsToOpen (I := SurfaceRealModel) (M := X) (A := ℝ)
          S 2 (deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1 theta) :=
        deRhamDifferential_restrictSmoothFormsToOpen
          (I := SurfaceRealModel) (A := ℝ) S theta
      _ = restrictSmoothFormsToOpen (I := SurfaceRealModel) (M := X) (A := ℝ)
          S 2 omega := congrArg
        (restrictSmoothFormsToOpen (I := SurfaceRealModel) (M := X) (A := ℝ) S 2)
        htheta
      _ = _ := smoothFormCompactZeroExtension_restrict
        SurfaceRealModel S KS hKScompact
        (deRhamDifferential (I := SurfaceRealModel) (M := S) (A := ℝ) 1 alpha)
        hdalphaZero
  have hetaClosed :
      deRhamDifferential (I := SurfaceRealModel) (M := S) (A := ℝ) 1 etaForm = 0 := by
    change deRhamDifferential (I := SurfaceRealModel) (M := S) (A := ℝ) 1
      (alpha - thetaS) = 0
    rw [map_sub, hthetaS, sub_self]
  refine ⟨⟨etaForm, hetaClosed⟩, ?_⟩
  have hAlphaQ :
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := Q) (V := S) (inf_le_left.trans le_sup_left) 1 alpha =
        restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := Q) (V := W) inf_le_left 1
          (exteriorCutoffAngularCollarOneForm W phi v) := by
    calc
      _ = restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := Q) (V := W) inf_le_left 1
          (restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
            (W := W) (V := S) le_sup_left 1 alpha) :=
        restrictSmoothFormsOfLE_trans Q W S inf_le_left le_sup_left alpha
      _ = _ := congrArg
        (restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := Q) (V := W) inf_le_left 1) halphaW
  have hThetaQ :
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := Q) (V := S) (inf_le_left.trans le_sup_left) 1 thetaS =
        (0 : SmoothForms (I := SurfaceRealModel) (M := Q) ℝ 1) := by
    apply DifferentialForm.ext
    intro x
    let xS : S := TopologicalSpace.Opens.inclusion
      (inf_le_left.trans le_sup_left) x
    have hxNotV : (x : X) ∉ V := by
      intro hxV
      exact hV.subset hxV (subset_closure x.2.2)
    have hthetaZero : theta.toFun (x : X) = 0 := hthetaSupport (x : X) hxNotV
    have hthetaSZero : thetaS.toFun xS = 0 := by
      exact restrictSmoothFormsToOpen_toFun_eq_zero_of_ambient_eq_zero
        SurfaceRealModel S theta xS hthetaZero
    simp only [restrictSmoothFormsOfLE]
    change (thetaS.toFun xS).compContinuousLinearMap _ = 0
    rw [hthetaSZero]
    rfl
  change restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
      (W := Q) (V := S) (inf_le_left.trans le_sup_left) 1
      (alpha - thetaS) = _
  rw [map_sub, hAlphaQ, hThetaQ, sub_zero]

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  An exterior component with its collar has nonzero \(H^1\)
statement:
  Let \(V\) be an exterior component incident to a full annular collar
  \(W\cong S^1\times\mathbb R\), with the domain on the negative side.  Then
  \[
    H^1_{\mathrm{dR}}(W\cup V;\mathbb R)\neq0.
  \]
proof:
  Extend the angular form to a closed form on \(W\cup V\).  Its restriction
  to the negative half-collar is the angular form, whose cohomology class is
  nonzero.  If the extension were exact, its restriction would be exact as
  well, a contradiction.
-/
theorem IsExteriorComponent.not_subsingleton_deRhamH1_exteriorComponentCollarUnion
    (E : SmoothRelativelyCompactExhaustion X)
    (D : SmoothBoundaryDomain X)
    (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ)
    (hside : ∀ y : W, ((y : X) ∈ D.carrier ↔ (phi y).2 < 0))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2))
    (V : Set X) (hVext : IsExteriorComponent (closure D.carrier) V)
    (p : frontier D.carrier) (hpW : (p : X) ∈ W)
    (hpV : (p : X) ∈ frontier V)
    (v : Circle) :
    ¬ Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := exteriorComponentCollarUnion W V
          (hVext.isComponentOf.isOpen_of_isOpen
            isClosed_closure.isOpen_compl)) (A := ℝ) 1) := by
  let hVopen := hVext.isComponentOf.isOpen_of_isOpen
    isClosed_closure.isOpen_compl
  let S := exteriorComponentCollarUnion W V hVopen
  let Q := W ⊓ ⟨D.carrier, D.isOpen⟩
  let hQS : Q ≤ S := inf_le_left.trans le_sup_left
  let psi := sidePreservingAnnularCollarDomainRestriction D W phi hside
  rcases hVext.exists_closed_exteriorAngularExtension
      E D W phi hexteriorSide V p hpW hpV v with ⟨eta, heta⟩
  let betaNeg : DeRhamClosedForms (I := AnnularCylinderModel)
      (M := negativeAnnularCylinderOpen) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionToOpen (I := AnnularCylinderModel)
      (A := ℝ) negativeAnnularCylinderOpen 1 (annularAngularClosedForm v)
  let betaQ : DeRhamClosedForms (I := SurfaceRealModel)
      (M := Q) (A := ℝ) 1 :=
    deRhamClosedFormsPullbackDiffeomorph SurfaceRealModel
      AnnularCylinderModel psi 1 betaNeg
  let etaQ : DeRhamClosedForms (I := SurfaceRealModel)
      (M := Q) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
      hQS 1 eta
  have hetaQForm : etaQ.1 = betaQ.1 := by
    calc
      etaQ.1 = restrictSmoothFormsOfLE (I := SurfaceRealModel)
          (M := X) (A := ℝ) (W := Q) (V := S) hQS 1 eta.1 := rfl
      _ = restrictSmoothFormsOfLE (I := SurfaceRealModel)
          (M := X) (A := ℝ) (W := Q) (V := W) inf_le_left 1
            (exteriorCutoffAngularCollarOneForm W phi v) := heta
      _ = smoothFormsPullbackDiffeomorph SurfaceRealModel
          AnnularCylinderModel psi 1
          (restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
            negativeAnnularCylinderOpen 1 (annularAngularClosedForm v).1) :=
        restrict_exteriorCutoffAngularCollarOneForm_domain_eq_pullback_negative
          D W phi hside v
      _ = betaQ.1 := rfl
  have hetaQ : etaQ = betaQ := by
    apply Subtype.ext
    exact hetaQForm
  have hbetaNeg :
      (DeRhamExactClosedForms (I := AnnularCylinderModel)
        (M := negativeAnnularCylinderOpen) (A := ℝ) 1).mkQ betaNeg ≠ 0 := by
    simpa [betaNeg] using annularAngularClosedForm_negative_class_ne_zero v
  have hbetaQ :
      (DeRhamExactClosedForms (I := SurfaceRealModel)
        (M := Q) (A := ℝ) 1).mkQ betaQ ≠ 0 := by
    intro hzero
    have hpullzero :
        deRhamCohomologyPullbackDiffeomorph SurfaceRealModel
            AnnularCylinderModel psi 1
            ((DeRhamExactClosedForms (I := AnnularCylinderModel)
              (M := negativeAnnularCylinderOpen) (A := ℝ) 1).mkQ betaNeg) = 0 := by
      simpa [betaQ, deRhamCohomologyPullbackDiffeomorph,
        Submodule.mapQ_apply] using hzero
    have hinverse := congrArg
      (deRhamCohomologyPullbackDiffeomorph AnnularCylinderModel
        SurfaceRealModel psi.symm 1) hpullzero
    have hinverseZero :
        deRhamCohomologyPullbackDiffeomorph AnnularCylinderModel
          SurfaceRealModel psi.symm 1
          (0 : DeRhamCohomology (I := SurfaceRealModel)
            (M := Q) (A := ℝ) 1) = 0 :=
      LinearMap.map_zero _
    rw [hinverseZero,
      deRhamCohomologyPullbackDiffeomorph_symm_comp] at hinverse
    exact hbetaNeg hinverse
  have hetaQClass :
      (DeRhamExactClosedForms (I := SurfaceRealModel)
        (M := Q) (A := ℝ) 1).mkQ etaQ ≠ 0 := by
    rw [hetaQ]
    exact hbetaQ
  intro hsub
  letI : Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := S) (A := ℝ) 1) := hsub
  have hzeroS :
      (DeRhamExactClosedForms (I := SurfaceRealModel)
        (M := S) (A := ℝ) 1).mkQ eta = 0 :=
    Subsingleton.elim _ _
  have hzeroQ := congrArg
    (deRhamCohomologyRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
      hQS 1) hzeroS
  have hrestrictionZero :
      deRhamCohomologyRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
          hQS 1 (0 : DeRhamCohomology (I := SurfaceRealModel)
            (M := S) (A := ℝ) 1) = 0 :=
    LinearMap.map_zero _
  rw [hrestrictionZero] at hzeroQ
  apply hetaQClass
  simpa [etaQ, deRhamCohomologyRestrictionOfLE,
    Submodule.mapQ_apply] using hzeroQ

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  Removing one exterior component preserves vanishing first cohomology
statement:
  Let \(X\) be a noncompact Riemann surface with
  \(H^1_{\mathrm{dR}}(X;\mathbb R)=0\).  If \(D\subseteq X\) is a
  preconnected smooth relatively compact domain and \(V\) is an exterior
  component of \(X\setminus\overline D\), then
  \[
    H^1_{\mathrm{dR}}(X\setminus\overline V;\mathbb R)=0.
  \]
proof:
  Choose an annular collar of the boundary component incident to \(V\).
  The collar together with \(V\) has nonzero first cohomology, while its
  overlap with \(X\setminus\overline V\) is an annulus.  The annular
  Mayer--Vietoris criterion and the vanishing on \(X\) give the result.
-/
theorem IsExteriorComponent.subsingleton_deRhamH1_complementComponentClosureOpen
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (hnoncompact : ¬ CompactSpace X)
    (E : SmoothRelativelyCompactExhaustion X)
    (D : SmoothBoundaryDomain X)
    (hDpre : IsPreconnected D.carrier)
    (V : Set X) (hVext : IsExteriorComponent (closure D.carrier) V) :
    Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := complementComponentClosureOpen V) (A := ℝ) 1) := by
  letI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  letI : SigmaCompactSpace X := by infer_instance
  let hV : IsComponentOf V (closure D.carrier)ᶜ := hVext.isComponentOf
  rcases exists_sidePreservingAnnularCollar_of_complementComponent
      hnoncompact D D.nonempty hDpre V hV with
    ⟨p, W, phi, hpV, hpW, hfrontierW, hside, hexteriorSide⟩
  let hVopen : IsOpen V :=
    hV.isOpen_of_isOpen isClosed_closure.isOpen_compl
  let U : TopologicalSpace.Opens X :=
    exteriorComponentCollarUnion W V hVopen
  let R : TopologicalSpace.Opens X := complementComponentClosureOpen V
  have hcover : U ⊔ R = ⊤ := by
    exact exteriorComponentCollarUnion_sup_complementComponentClosureOpen
      W V hVopen hfrontierW
  let psi : (U ⊓ R : TopologicalSpace.Opens X) ≃ₘ⟮
      SurfaceRealModel, AnnularCylinderModel⟯ Circle × ℝ :=
    exteriorComponentCollarMayerVietorisOverlapDiffeomorph
      D W phi hside hexteriorSide V hV p hpW hpV
  have hleft : ¬ Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := U) (A := ℝ) 1) := by
    simpa [U, hVopen] using
      hVext.not_subsingleton_deRhamH1_exteriorComponentCollarUnion
        E D W phi hside hexteriorSide V p hpW hpV
          (annularOpposite 1)
  simpa [R] using
    deRhamH1_subsingleton_of_mayerVietoris_annular_and_left_nontrivial
      SurfaceRealModel U R hcover psi (annularOpposite 1) hleft

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  Vanishing first cohomology for the complement of an exterior component
statement:
  Let \(D\) be a preconnected smooth relatively compact domain in a
  noncompact Riemann surface \(X\) with
  \(H^1_{\mathrm{dR}}(X;\mathbb R)=0\).  If \(V\) is an exterior component
  of \(X\setminus\overline D\) and \(D=X\setminus\overline V\), then
  \(H^1_{\mathrm{dR}}(D;\mathbb R)=0\).
proof:
  Identify \(D\) with the open complement of \(\overline V\) and apply the
  preceding exterior-component removal theorem.
-/
theorem SmoothBoundaryDomain.deRhamH1Zero_of_exteriorComponent_complement
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (hnoncompact : ¬ CompactSpace X)
    (E : SmoothRelativelyCompactExhaustion X)
    (D : SmoothBoundaryDomain X)
    (hDpre : IsPreconnected D.carrier)
    (V : Set X) (hVext : IsExteriorComponent (closure D.carrier) V)
    (hcarrier : D.carrier = (closure V)ᶜ) :
    D.deRhamH1Zero := by
  let DU : TopologicalSpace.Opens X := ⟨D.carrier, D.isOpen⟩
  have hDU : DU = complementComponentClosureOpen V := by
    ext x
    exact Set.ext_iff.mp hcarrier x
  change Subsingleton
    (DeRhamCohomology (I := SurfaceRealModel) (M := DU) (A := ℝ) 1)
  rw [hDU]
  exact hVext.subsingleton_deRhamH1_complementComponentClosureOpen
    hnoncompact E D hDpre V

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
/--
%%handwave
name:
  Exterior complementary components imply vanishing domain \(H^1\)
statement:
  Let \(X\) be a noncompact Riemann surface with
  \(H^1_{\mathrm{dR}}(X;\mathbb R)=0\), and let \(D\subseteq X\) be a
  preconnected smooth relatively compact domain.  If every component of
  \(X\setminus\overline D\) is exterior, then
  \[
    H^1_{\mathrm{dR}}(D;\mathbb R)=0.
  \]
proof:
  There are finitely many complementary components.  Enumerate them and
  remove their closures one at a time.  Each removal has an annular overlap,
  while the removed exterior component together with its collar has nonzero
  first cohomology.  The finite annular Mayer--Vietoris induction preserves
  vanishing from \(X\) to the final open set, which is \(D\).
-/
theorem SmoothBoundaryDomain.deRhamH1Zero_of_all_complementComponents_exterior
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (hnoncompact : ¬ CompactSpace X)
    (E : SmoothRelativelyCompactExhaustion X)
    (D : SmoothBoundaryDomain X)
    (hDpre : IsPreconnected D.carrier)
    (hallExterior : ∀ V : Set X,
      IsComponentOf V (closure D.carrier)ᶜ →
        IsExteriorComponent (closure D.carrier) V) :
    D.deRhamH1Zero := by
  classical
  let I := {V : Set X // IsComponentOf V (closure D.carrier)ᶜ}
  have hcomponentsFinite : {V : Set X |
      IsComponentOf V (closure D.carrier)ᶜ}.Finite :=
    smoothBoundaryDomain_complement_components_finite D
  letI : Finite I := by simpa [I] using hcomponentsFinite
  letI : Fintype I := Fintype.ofFinite I
  let m := Fintype.card I
  let enum : Fin m ≃ I := (Fintype.equivFin I).symm
  have hcomponent (i : Fin m) :
      IsComponentOf (enum i : Set X) (closure D.carrier)ᶜ :=
    (enum i).property
  have hexterior (i : Fin m) :
      IsExteriorComponent (closure D.carrier) (enum i : Set X) :=
    hallExterior (enum i : Set X) (hcomponent i)
  let collar : (i : Fin m) →
      ComplementComponentCollarData D (enum i : Set X) (hcomponent i) :=
    fun i => Classical.choice
      (complementComponentCollarData_nonempty hnoncompact D hDpre
        (enum i : Set X) (hcomponent i))
  let removed (n : ℕ) : Set X :=
    ⋃ i ∈ (Finset.univ.filter fun i : Fin m => (i : ℕ) < n),
      closure (enum i : Set X)
  have hremovedClosed (n : ℕ) : IsClosed (removed n) := by
    dsimp [removed]
    exact isClosed_biUnion_finset fun _i _hi => isClosed_closure
  let R (n : ℕ) : TopologicalSpace.Opens X :=
    ⟨(removed n)ᶜ, (hremovedClosed n).isOpen_compl⟩
  let L (n : ℕ) : TopologicalSpace.Opens X :=
    if hn : n < m then
      exteriorComponentCollarUnion (collar ⟨n, hn⟩).W
        (enum ⟨n, hn⟩ : Set X)
        ((hcomponent ⟨n, hn⟩).isOpen_of_isOpen
          isClosed_closure.isOpen_compl)
    else ⊥
  have hremoved_mono {a b : ℕ} (hab : a ≤ b) :
      removed a ⊆ removed b := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨i, hx⟩
    rcases mem_iUnion.mp hx with ⟨hi, hxcl⟩
    refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨?_, hxcl⟩⟩
    rcases Finset.mem_filter.mp hi with ⟨_hiuniv, hia⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hia.trans_le hab⟩
  have hnext : ∀ n : ℕ, n < m → R (n + 1) ≤ R n := by
    intro n _hn x hx
    exact fun hxRemoved => hx (hremoved_mono (Nat.le_succ n) hxRemoved)
  have hleftSubset : ∀ n : ℕ, n < m → L n ≤ R n := by
    intro n hn x hxL
    simp only [L, dif_pos hn] at hxL
    intro hxRemoved
    rcases mem_iUnion.mp hxRemoved with ⟨j, hxRemoved⟩
    rcases mem_iUnion.mp hxRemoved with ⟨hj, hxjcl⟩
    have hjn : (j : ℕ) < n := (Finset.mem_filter.mp hj).2
    let i : Fin m := ⟨n, hn⟩
    have hij : (enum i : Set X) ≠ (enum j : Set X) := by
      intro heq
      have hieqj : i = j := enum.injective (Subtype.ext heq)
      have : n = (j : ℕ) := congrArg Fin.val hieqj
      omega
    exact Set.disjoint_left.mp
      (exteriorComponentCollarUnion_disjoint_componentClosure_of_ne
        D (collar i).W (collar i).phi
          (collar i).domain_side (collar i).exterior_side
          (enum i : Set X) (enum j : Set X)
          (hcomponent i) (hcomponent j)
          (collar i).p (collar i).p_mem_collar
          (collar i).p_mem_frontier hij) hxL hxjcl
  have hnot_removed_succ {n : ℕ} (hn : n < m) {x : X}
      (hxNotRemoved : x ∉ removed n)
      (hxNotCurrent : x ∉ closure (enum (⟨n, hn⟩ : Fin m) : Set X)) :
      x ∉ removed (n + 1) := by
    intro hxRemoved
    rcases mem_iUnion.mp hxRemoved with ⟨j, hxRemoved⟩
    rcases mem_iUnion.mp hxRemoved with ⟨hj, hxjcl⟩
    have hjlt : (j : ℕ) < n + 1 := (Finset.mem_filter.mp hj).2
    have hjle : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp (by simpa using hjlt)
    rcases lt_or_eq_of_le hjle with hjn | hjeq
    · apply hxNotRemoved
      exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjn⟩, hxjcl⟩⟩
    · apply hxNotCurrent
      have hji : j = (⟨n, hn⟩ : Fin m) := Fin.ext hjeq
      simpa [hji] using hxjcl
  have hclosureCurrent_subset_left {n : ℕ} (hn : n < m) :
      closure (enum (⟨n, hn⟩ : Fin m) : Set X) ⊆ (L n : Set X) := by
    intro x hxcl
    simp only [L, dif_pos hn]
    let i : Fin m := ⟨n, hn⟩
    let hVopen : IsOpen (enum i : Set X) :=
      (hcomponent i).isOpen_of_isOpen isClosed_closure.isOpen_compl
    by_cases hxV : x ∈ (enum i : Set X)
    · exact Or.inr hxV
    · left
      exact (collar i).frontier_subset_collar (by
        rw [frontier, hVopen.interior_eq]
        exact ⟨hxcl, hxV⟩)
  have hcover : ∀ n : ℕ, n < m →
      openWithinOpen (R n) (L n) ⊔
        openWithinOpen (R n) (R (n + 1)) = ⊤ := by
    intro n hn
    ext x
    constructor
    · intro _
      trivial
    · intro _
      change ((x : X) ∈ (L n : Set X)) ∨
        ((x : X) ∈ (R (n + 1) : Set X))
      by_cases hxCurrent : (x : X) ∈
          closure (enum (⟨n, hn⟩ : Fin m) : Set X)
      · exact Or.inl (hclosureCurrent_subset_left hn hxCurrent)
      · exact Or.inr
          (hnot_removed_succ hn x.2 hxCurrent)
  have hoverlap : ∀ (n : ℕ) (hn : n < m),
      (openWithinOpen (R n) (L n) ⊓
          openWithinOpen (R n) (R (n + 1)) :
        TopologicalSpace.Opens (R n)) =
      openWithinOpen (R n)
        (L n ⊓ complementComponentClosureOpen
          (enum (⟨n, hn⟩ : Fin m) : Set X)) := by
    intro n hn
    ext x
    change (((x : X) ∈ (L n : Set X)) ∧
        ((x : X) ∈ (R (n + 1) : Set X))) ↔
      ((x : X) ∈ (L n : Set X) ∧
        (x : X) ∉ closure (enum (⟨n, hn⟩ : Fin m) : Set X))
    constructor
    · rintro ⟨hxL, hxNext⟩
      refine ⟨hxL, ?_⟩
      intro hxCurrent
      apply hxNext
      exact mem_iUnion.mpr ⟨(⟨n, hn⟩ : Fin m), mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Nat.lt_succ_self n⟩, hxCurrent⟩⟩
    · rintro ⟨hxL, hxNotCurrent⟩
      exact ⟨hxL,
        hnot_removed_succ hn (hleftSubset n hn hxL) hxNotCurrent⟩
  have hoverlapSubset : ∀ (n : ℕ) (hn : n < m),
      L n ⊓ complementComponentClosureOpen
          (enum (⟨n, hn⟩ : Fin m) : Set X) ≤ R n := by
    intro n hn
    exact inf_le_left.trans (hleftSubset n hn)
  let phi : ∀ (n : ℕ) (hn : n < m),
      ((openWithinOpen (R n) (L n) ⊓
        openWithinOpen (R n) (R (n + 1)) :
          TopologicalSpace.Opens (R n))) ≃ₘ⟮SurfaceRealModel,
            AnnularCylinderModel⟯ Circle × ℝ := fun n hn => by
    let i : Fin m := ⟨n, hn⟩
    have hLn : L n = exteriorComponentCollarUnion (collar i).W
        (enum i : Set X)
        ((hcomponent i).isOpen_of_isOpen
          isClosed_closure.isOpen_compl) := by
      simp [L, hn, i]
    rw [hoverlap n hn, hLn]
    exact (openWithinOpenDiffeomorph (R n)
      (exteriorComponentCollarUnion (collar i).W (enum i : Set X)
          ((hcomponent i).isOpen_of_isOpen
            isClosed_closure.isOpen_compl) ⊓
        complementComponentClosureOpen (enum i : Set X))
      (by simpa [hLn] using hoverlapSubset n hn)).trans
        (exteriorComponentCollarMayerVietorisOverlapDiffeomorph
          D (collar i).W (collar i).phi
          (collar i).domain_side (collar i).exterior_side
          (enum i : Set X) (hcomponent i)
          (collar i).p (collar i).p_mem_collar
          (collar i).p_mem_frontier)
  have hleft : ∀ n : ℕ, n < m → ¬ Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := L n) (A := ℝ) 1) := by
    intro n hn
    let i : Fin m := ⟨n, hn⟩
    have hLn : L n = exteriorComponentCollarUnion (collar i).W
        (enum i : Set X)
        ((hcomponent i).isOpen_of_isOpen
          isClosed_closure.isOpen_compl) := by
      simp [L, hn, i]
    rw [hLn]
    exact
      (hexterior i).not_subsingleton_deRhamH1_exteriorComponentCollarUnion
        E D (collar i).W (collar i).phi
          (collar i).domain_side (collar i).exterior_side
          (enum i : Set X) (collar i).p
          (collar i).p_mem_collar (collar i).p_mem_frontier
          (annularOpposite 1)
  have hRzero : Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := R 0) (A := ℝ) 1) := by
    have hR0 : R 0 = (⊤ : TopologicalSpace.Opens X) := by
      ext x
      simp [R, removed]
    rw [hR0]
    exact deRhamCohomology_subsingleton_of_diffeomorphic
      SurfaceRealModel SurfaceRealModel
        (Classical.choice (topOpen_diffeomorph (M := X) SurfaceRealModel)).symm
        1 (inferInstance : Subsingleton
          (DeRhamCohomology (I := SurfaceRealModel)
            (M := X) (A := ℝ) 1))
  have hRm : R m = (⟨D.carrier, D.isOpen⟩ : TopologicalSpace.Opens X) := by
    ext x
    constructor
    · intro hxR
      by_contra hxD
      by_cases hxClosureD : x ∈ closure D.carrier
      · have hxFrontier : x ∈ frontier D.carrier := by
          rw [frontier, D.isOpen.interior_eq]
          exact ⟨hxClosureD, hxD⟩
        let p : frontier D.carrier := ⟨x, hxFrontier⟩
        rcases smoothBoundaryDomain_connected_boundary_component_incident_component
            D p with ⟨V, hVfrontier⟩
        let i : Fin m := enum.symm V
        apply hxR
        exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr
          ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_univ i, i.isLt⟩,
            frontier_subset_closure
              (by simpa [i] using hVfrontier p mem_connectedComponent)⟩⟩
      · let V : Set X := connectedComponentIn (closure D.carrier)ᶜ x
        have hxComp : x ∈ V := mem_connectedComponentIn hxClosureD
        have hVcomp : IsComponentOf V (closure D.carrier)ᶜ :=
          isComponentOf_connectedComponentIn hxClosureD
        let Vi : I := ⟨V, hVcomp⟩
        let i : Fin m := enum.symm Vi
        apply hxR
        exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, i.isLt⟩,
            subset_closure (by simpa [i, Vi, V] using hxComp)⟩⟩
    · intro hxD hxRemoved
      rcases mem_iUnion.mp hxRemoved with ⟨i, hxRemoved⟩
      rcases mem_iUnion.mp hxRemoved with ⟨_hi, hxClosure⟩
      exact Set.disjoint_left.mp
        (smoothBoundaryDomain_carrier_disjoint_complement_component_closure
          D (enum i : Set X) (hcomponent i)) hxD hxClosure
  have hfinal :=
    subsingleton_deRhamH1_of_bounded_nested_annular_removals
      m R L hnext hleftSubset hcover phi (fun _ => annularOpposite 1)
        hleft hRzero
  change Subsingleton
    (DeRhamCohomology (I := SurfaceRealModel)
      (M := (⟨D.carrier, D.isOpen⟩ : TopologicalSpace.Opens X))
      (A := ℝ) 1)
  rw [← hRm]
  exact hfinal

end

end JJMath.Uniformization
