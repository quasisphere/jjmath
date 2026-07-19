import JJMath.Uniformization.AnnularMassTransport
import JJMath.Uniformization.SurfaceEndPath

/-!
# Mass transport through exterior components

Nested exterior components along a smooth exhaustion form a locally finite
family.  Consequently the abstract pathwise mass-transport construction
applies to any compactly supported two-form carried by an initial coordinate
chart in such an exterior chain.
-/

open Set
open scoped Manifold ContDiff Topology
open JJMath.Manifold

namespace JJMath.Uniformization

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

omit [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X] in
/-- Exterior components of the complements of successive exhaustion
closures have locally finite closures.

%%handwave
name: Local finiteness of exterior components along an exhaustion
statement:
  Let $(\Omega_n)$ be a smooth relatively compact exhaustion and, for each $n$, let $U_n$ be an exterior component of $X\setminus\overline{\Omega_{N+n}}$. Then the family $(\overline{U_n})$ is locally finite.
proof:
  Given $y$, choose an exhaustion member $\Omega_q$ containing it. For $n\ge q$, monotonicity puts $\Omega_q$ inside $\overline{\Omega_{N+n}}$, while $U_n$ lies in its complement; hence $\overline{U_n}$ misses $\Omega_q$. Only the finitely many indices $n<q$ can meet this neighborhood.
-/
theorem locallyFinite_closure_exteriorComponents_along_smoothExhaustion
    (E : SmoothRelativelyCompactExhaustion X) (N : ℕ)
    (U : ℕ → Set X)
    (hU : ∀ n : ℕ,
      IsExteriorComponent (closure (E.domain (N + n)).carrier) (U n)) :
    LocallyFinite (fun n => closure (U n)) := by
  intro y
  obtain ⟨q, hyq⟩ := E.exhausts y
  refine ⟨(E.domain q).carrier, (E.domain q).isOpen.mem_nhds hyq, ?_⟩
  apply Set.Finite.subset (Finset.finite_toSet (Finset.range q))
  intro n hn
  by_contra hnrange
  have hqn : q ≤ n := Nat.le_of_not_gt (by simpa using hnrange)
  obtain ⟨z, hzclosure, hzq⟩ := hn
  have hclosureCompl : closure (U n) ⊆ (E.domain q).carrierᶜ := by
    apply closure_minimal
    · intro w hwU hwq
      exact (hU n).subset_compl hwU
        (subset_closure
          (smoothRelativelyCompactExhaustion_carrier_mono E
            (hqn.trans (Nat.le_add_left n N)) hwq))
    · exact (E.domain q).isOpen.isClosed_compl
  exact hclosureCompl hzclosure hzq

/-- A compactly supported two-form carried by the first chart of a nested
exterior path chain has a global primitive supported in the union of the
exterior components.

%%handwave
name: Supported primitive along a nested exterior chain
statement:
  Let $U_n$ be exterior components along an exhaustion, joined by paths through $U_n$. If a smooth two-form is compactly supported in a planar chart inside $U_0$, then it has a global primitive $\theta$ that vanishes outside $\bigcup_nU_n$.
proof:
  Join the chart's marked point to the first path chain inside $U_0$, forming a compatible transport sequence. The exterior closures are locally finite, so the locally finite corridor-transport theorem yields the primitive and its support bound.
-/
theorem exists_primitive_of_compactSupport_exteriorChain_with_support
    (E : SmoothRelativelyCompactExhaustion X) (N : ℕ)
    (U : ℕ → Set X) (x : ℕ → X)
    (gamma : ∀ n : ℕ, Path (x n) (x (n + 1)))
    (hU : ∀ n : ℕ,
      IsExteriorComponent (closure (E.domain (N + n)).carrier) (U n))
    (hx : ∀ n : ℕ, x n ∈ U n)
    (hgamma : ∀ n : ℕ, ∀ t : unitInterval, gamma n t ∈ U n)
    (V0 : TopologicalSpace.Opens X) (hV0 : V0 ≤ U 0)
    (y0 : V0)
    (phi0 : Nonempty
      (V0 ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen))
    (K0 : Set V0) (hK0 : IsCompact K0)
    (omega : JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := X) ℝ 2)
    (hzero : ∀ y : X,
      y ∉ smoothFormCompactCore V0 K0 → omega.toFun y = 0) :
    ∃ theta : JJMath.Manifold.SmoothForms
        (I := SurfaceRealModel) (M := X) ℝ 1,
      JJMath.Manifold.deRhamDifferential
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1 theta = omega ∧
      ∀ y : X, y ∉ ⋃ n : ℕ, U n → theta.toFun y = 0 := by
  have hU0path : IsPathConnected (U 0) :=
    (hU 0).isComponentOf.isPathConnected_of_compl_isClosed isClosed_closure
  have hx1U0 : x 1 ∈ U 0 := by
    simpa using hgamma 0 1
  have hjoined : JoinedIn (U 0) (y0 : X) (x 1) :=
    hU0path.joinedIn (y0 : X) (hV0 y0.2) (x 1) hx1U0
  let x' : ℕ → X
    | 0 => (y0 : X)
    | n + 1 => x (n + 1)
  let gamma' : ∀ n : ℕ, Path (x' n) (x' (n + 1))
    | 0 => hjoined.somePath
    | n + 1 => gamma (n + 1)
  have hx' : ∀ n : ℕ, x' n ∈ U n := by
    intro n
    cases n with
    | zero => exact hV0 y0.2
    | succ n => exact hx (n + 1)
  have hgamma' : ∀ n : ℕ, ∀ t : unitInterval, gamma' n t ∈ U n := by
    intro n t
    cases n with
    | zero => exact hjoined.somePath_mem t
    | succ n => exact hgamma (n + 1) t
  let W : ℕ → TopologicalSpace.Opens X := fun n =>
    ⟨U n, (hU n).isComponentOf.isOpen_of_isOpen
      isClosed_closure.isOpen_compl⟩
  let initial : CompactSupportTransportState W x' 0 :=
    { chartOpen := V0
      chartOpen_subset := hV0
      point_mem := y0.2
      planarChart := phi0
      form := omega
      core := K0
      core_isCompact := hK0
      form_zero_outside := hzero }
  have hlocW : LocallyFinite (fun n => closure (W n : Set X)) := by
    simpa [W] using
      locallyFinite_closure_exteriorComponents_along_smoothExhaustion E N U hU
  rcases exists_primitive_of_compactSupport_transport_along_paths_with_support
      W x' gamma' hgamma' (fun n => hx' (n + 1)) hlocW initial with
    ⟨theta, htheta, hthetaSupport⟩
  refine ⟨theta, htheta, ?_⟩
  intro y hy
  apply hthetaSupport y
  simpa [W] using hy

/-- A compactly supported two-form carried by the first chart of a nested
exterior path chain has a global primitive.

%%handwave
name: Primitive along a nested exterior chain
statement:
  Under the same exterior-chain hypotheses, a two-form compactly supported in the initial planar chart is globally exact.
proof:
  Apply the supported exterior-chain theorem and discard the support conclusion.
-/
theorem exists_primitive_of_compactSupport_exteriorChain
    (E : SmoothRelativelyCompactExhaustion X) (N : ℕ)
    (U : ℕ → Set X) (x : ℕ → X)
    (gamma : ∀ n : ℕ, Path (x n) (x (n + 1)))
    (hU : ∀ n : ℕ,
      IsExteriorComponent (closure (E.domain (N + n)).carrier) (U n))
    (hx : ∀ n : ℕ, x n ∈ U n)
    (hgamma : ∀ n : ℕ, ∀ t : unitInterval, gamma n t ∈ U n)
    (V0 : TopologicalSpace.Opens X) (hV0 : V0 ≤ U 0)
    (y0 : V0)
    (phi0 : Nonempty
      (V0 ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen))
    (K0 : Set V0) (hK0 : IsCompact K0)
    (omega : JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := X) ℝ 2)
    (hzero : ∀ y : X,
      y ∉ smoothFormCompactCore V0 K0 → omega.toFun y = 0) :
    ∃ theta : JJMath.Manifold.SmoothForms
        (I := SurfaceRealModel) (M := X) ℝ 1,
      JJMath.Manifold.deRhamDifferential
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1 theta = omega := by
  rcases exists_primitive_of_compactSupport_exteriorChain_with_support
      E N U x gamma hU hx hgamma V0 hV0 y0 phi0 K0 hK0 omega hzero with
    ⟨theta, htheta, _hsupport⟩
  exact ⟨theta, htheta⟩

/-- A two-form compactly supported in a full-plane coordinate chart inside
an exterior component is globally exact, with a primitive supported in that
component.  The compact mass is first moved to the nested exterior chain and
is then transported to infinity.

%%handwave
name: Supported primitive for chartwise mass in an exterior component
statement:
  Let $V$ be an exterior component and let $\omega$ be supported in a compact subset of a full-plane coordinate chart contained in $V$. Then there is a smooth one-form $\theta$ with $d\theta=\omega$ and $\theta=0$ on $X\setminus V$.
proof:
  Choose an escaping nested chain of exterior components inside $V$. First transport the compact mass along a path in $V$ into the initial member of that chain; then transport the remainder to infinity along the chain. Add the two corrections, whose supports both remain in $V$.
-/
theorem IsExteriorComponent.exists_primitive_of_compactSupport_in_coordinateChart_with_support
    (E : SmoothRelativelyCompactExhaustion X)
    {K V : Set X} (hKcompact : IsCompact K)
    (hV : IsExteriorComponent K V)
    (V0 : TopologicalSpace.Opens X) (hV0 : V0 ≤ V)
    (y0 : V0)
    (phi0 : V0 ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (K0 : Set V0) (hK0 : IsCompact K0)
    (omega : JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := X) ℝ 2)
    (hzero : ∀ y : X,
      y ∉ smoothFormCompactCore V0 K0 → omega.toFun y = 0) :
    ∃ theta : JJMath.Manifold.SmoothForms
        (I := SurfaceRealModel) (M := X) ℝ 1,
      JJMath.Manifold.deRhamDifferential
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1 theta = omega ∧
      ∀ y : X, y ∉ V → theta.toFun y = 0 := by
  rcases hV.exists_escaping_path_chain_along_smoothExhaustion E hKcompact with
    ⟨N, U, x, gamma, _hK, hU, hU0V, hUanti, hx, hgamma, _hescape⟩
  let Vopen : TopologicalSpace.Opens X :=
    ⟨V, hV.isComponentOf.isOpen_of_isOpen hKcompact.isClosed.isOpen_compl⟩
  let U0open : TopologicalSpace.Opens X :=
    ⟨U 0, (hU 0).isComponentOf.isOpen_of_isOpen
      isClosed_closure.isOpen_compl⟩
  have hVpath : IsPathConnected V :=
    hV.isComponentOf.isPathConnected_of_compl_isClosed hKcompact.isClosed
  have hyV : (y0 : X) ∈ V := hV0 y0.2
  have hx0V : x 0 ∈ V := hU0V (hx 0)
  have hjoined : JoinedIn V (y0 : X) (x 0) :=
    hVpath.joinedIn (y0 : X) hyV (x 0) hx0V
  let delta : Path (y0 : X) (x 0) := hjoined.somePath
  obtain ⟨eta0, beta0, Vtail, Ktail, hx0Vtail, hVtail,
      hphiTail, hKtail, hd0, heta0, hbeta0⟩ :=
    exists_compactSupport_transport_along_path
      Vopen U0open V0 phi0 delta
      (fun t => hjoined.somePath_mem t) (hx 0) y0.2 hV0
      K0 hK0 omega hzero
  have hVtailU0 : Vtail ≤ U 0 := hVtail.trans inf_le_right
  obtain ⟨thetaTail, hthetaTail, hthetaTailSupport⟩ :=
    exists_primitive_of_compactSupport_exteriorChain_with_support
      E N U x gamma hU hx hgamma Vtail hVtailU0
      ⟨x 0, hx0Vtail⟩ hphiTail Ktail hKtail beta0 hbeta0
  refine ⟨eta0 + thetaTail, ?_, ?_⟩
  · rw [map_add, hd0, hthetaTail]
    abel
  · intro y hyV
    change eta0.toFun y + thetaTail.toFun y = 0
    rw [heta0 y hyV]
    rw [hthetaTailSupport y]
    · exact add_zero 0
    · intro hyUnion
      rcases mem_iUnion.mp hyUnion with ⟨n, hyn⟩
      exact hyV (hU0V (hUanti (Nat.zero_le n) hyn))

/-- A two-form compactly supported in a full-plane coordinate chart inside
an exterior component is globally exact.

%%handwave
name: Exactness of chartwise compact mass in an exterior component
statement:
  A smooth two-form compactly supported in a full-plane coordinate chart inside an exterior component is globally exact.
proof:
  Apply the supported chartwise primitive theorem and forget the support property.
-/
theorem IsExteriorComponent.exists_primitive_of_compactSupport_in_coordinateChart
    (E : SmoothRelativelyCompactExhaustion X)
    {K V : Set X} (hKcompact : IsCompact K)
    (hV : IsExteriorComponent K V)
    (V0 : TopologicalSpace.Opens X) (hV0 : V0 ≤ V)
    (y0 : V0)
    (phi0 : V0 ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (K0 : Set V0) (hK0 : IsCompact K0)
    (omega : JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := X) ℝ 2)
    (hzero : ∀ y : X,
      y ∉ smoothFormCompactCore V0 K0 → omega.toFun y = 0) :
    ∃ theta : JJMath.Manifold.SmoothForms
        (I := SurfaceRealModel) (M := X) ℝ 1,
      JJMath.Manifold.deRhamDifferential
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1 theta = omega := by
  rcases hV.exists_primitive_of_compactSupport_in_coordinateChart_with_support
      E hKcompact V0 hV0 y0 phi0 K0 hK0 omega hzero with
    ⟨theta, htheta, _hsupport⟩
  exact ⟨theta, htheta⟩

/--
%%handwave
name:
  Compactly supported two-forms in an exterior component have supported primitives
statement:
  Let \(V\) be an exterior component of \(X\setminus K\), and let \(C\subseteq
  V\) be compact.  If a smooth two-form \(\omega\) vanishes outside \(C\),
  then there is a smooth one-form \(\theta\) on \(X\) such that
  \[
    d\theta=\omega,
    \qquad
    \theta|_{X\setminus V}=0.
  \]
proof:
  Cover \(C\) by finitely many planar coordinate neighborhoods contained in
  \(V\), and split \(\omega\) with a subordinate smooth partition of unity.
  Each piece has a primitive whose compact support can be transported along
  the exterior component to infinity while remaining in \(V\).  Summing the
  finitely many primitives gives \(\theta\) with the stated derivative and
  support.
-/
theorem IsExteriorComponent.exists_primitive_of_compactSupport_with_support
    (E : SmoothRelativelyCompactExhaustion X)
    {K V C : Set X} (hKcompact : IsCompact K)
    (hV : IsExteriorComponent K V)
    (hCcompact : IsCompact C) (hCV : C ⊆ V)
    (omega : JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := X) ℝ 2)
    (hzero : ∀ y : X, y ∉ C → omega.toFun y = 0) :
    ∃ theta : JJMath.Manifold.SmoothForms
        (I := SurfaceRealModel) (M := X) ℝ 1,
      JJMath.Manifold.deRhamDifferential
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1 theta = omega ∧
      ∀ y : X, y ∉ V → theta.toFun y = 0 := by
  classical
  let U : C → TopologicalSpace.Opens X := fun p ↦
    Classical.choose
      (exists_complexPlanarChart_subordinate
        ⟨V, hV.isComponentOf.isOpen_of_isOpen
          hKcompact.isClosed.isOpen_compl⟩ (p : X) (hCV p.2))
  have hpU : ∀ p : C, (p : X) ∈ U p := fun p ↦
    (Classical.choose_spec
      (exists_complexPlanarChart_subordinate
        ⟨V, hV.isComponentOf.isOpen_of_isOpen
          hKcompact.isClosed.isOpen_compl⟩ (p : X) (hCV p.2))).1
  have hUV : ∀ p : C, U p ≤
      ⟨V, hV.isComponentOf.isOpen_of_isOpen
        hKcompact.isClosed.isOpen_compl⟩ := fun p ↦
    (Classical.choose_spec
      (exists_complexPlanarChart_subordinate
        ⟨V, hV.isComponentOf.isOpen_of_isOpen
          hKcompact.isClosed.isOpen_compl⟩ (p : X) (hCV p.2))).2.1
  have hphiU : ∀ p : C, Nonempty
      (U p ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯
        complexPlanarModelOpen) := fun p ↦
    (Classical.choose_spec
      (exists_complexPlanarChart_subordinate
        ⟨V, hV.isComponentOf.isOpen_of_isOpen
          hKcompact.isClosed.isOpen_compl⟩ (p : X) (hCV p.2))).2.2
  have hcover : C ⊆ ⋃ p : C, (U p : Set X) := by
    intro y hyC
    exact mem_iUnion.mpr ⟨⟨y, hyC⟩, hpU ⟨y, hyC⟩⟩
  rcases hCcompact.elim_finite_subcover
      (fun p : C ↦ (U p : Set X)) (fun p ↦ (U p).isOpen) hcover with
    ⟨t, ht⟩
  let J := {p : C // p ∈ t}
  let coverOpen : Option J → Set X
    | none => Cᶜ
    | some j => U (j : C)
  have hcoverOpen : ∀ i : Option J, IsOpen (coverOpen i) := by
    intro i
    cases i with
    | none => exact hCcompact.isClosed.isOpen_compl
    | some j => exact (U (j : C)).isOpen
  have hcoverUniv : (univ : Set X) ⊆ ⋃ i : Option J, coverOpen i := by
    intro y _hy
    by_cases hyC : y ∈ C
    · have hyt := ht hyC
      rcases mem_iUnion.mp hyt with ⟨p, hp⟩
      rcases mem_iUnion.mp hp with ⟨hpt, hyp⟩
      exact mem_iUnion.mpr ⟨some ⟨p, hpt⟩, hyp⟩
    · exact mem_iUnion.mpr ⟨none, hyC⟩
  letI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  letI : SigmaCompactSpace X := by infer_instance
  rcases SmoothPartitionOfUnity.exists_isSubordinate
      SurfaceRealModel isClosed_univ coverOpen hcoverOpen hcoverUniv with
    ⟨rho, hrho⟩
  let piece : Option J → JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := X) ℝ 2 := fun i ↦
    JJMath.Manifold.smoothFormsPointwiseSMul
      (I := SurfaceRealModel) (M := X) (A := ℝ) (rho i) omega
  have hpiece_exact : ∀ i : Option J,
      ∃ theta : JJMath.Manifold.SmoothForms
          (I := SurfaceRealModel) (M := X) ℝ 1,
        JJMath.Manifold.deRhamDifferential
          (I := SurfaceRealModel) (M := X) (A := ℝ) 1 theta = piece i ∧
        ∀ y : X, y ∉ V → theta.toFun y = 0 := by
    intro i
    cases i with
    | none =>
        have hpiece_zero : piece none = 0 := by
          apply DifferentialForm.ext
          intro y
          by_cases hyC : y ∈ C
          · apply JJMath.Manifold.smoothFormsPointwiseSMul_eq_zero_of_notMem_tsupport
            intro hysupport
            exact (hrho none hysupport) hyC
          · simp [piece, JJMath.Manifold.smoothFormsPointwiseSMul_toFun,
              hzero y hyC]
        refine ⟨0, ?_, ?_⟩
        · rw [map_zero, hpiece_zero]
        · intro y _hy
          rfl
    | some j =>
        let Cj : Set X := C ∩ tsupport (rho (some j))
        have hCjcompact : IsCompact Cj :=
          hCcompact.inter_right (isClosed_tsupport (rho (some j)))
        have hCjU : Cj ⊆ U (j : C) := by
          intro y hy
          exact hrho (some j) hy.2
        let Kj : Set (U (j : C)) :=
          smoothFormCompactCoreInOpen (U (j : C)) Cj
        have hKjcompact : IsCompact Kj :=
          smoothFormCompactCoreInOpen_isCompact
            (U (j : C)) Cj hCjcompact hCjU
        have hpiece_zero : ∀ y : X,
            y ∉ smoothFormCompactCore (U (j : C)) Kj →
              (piece (some j)).toFun y = 0 := by
          intro y hy
          have hyCj : y ∉ Cj := by
            rwa [smoothFormCompactCore_coreInOpen
              (U (j : C)) Cj hCjU] at hy
          by_cases hyC : y ∈ C
          · apply JJMath.Manifold.smoothFormsPointwiseSMul_eq_zero_of_notMem_tsupport
            intro hysupport
            exact hyCj ⟨hyC, hysupport⟩
          · simp [piece, JJMath.Manifold.smoothFormsPointwiseSMul_toFun,
              hzero y hyC]
        exact hV.exists_primitive_of_compactSupport_in_coordinateChart_with_support
          E hKcompact (U (j : C)) (hUV (j : C))
          ⟨(j : C), hpU (j : C)⟩ (Classical.choice (hphiU (j : C)))
          Kj hKjcompact (piece (some j)) hpiece_zero
  choose theta htheta hthetaSupport using hpiece_exact
  refine ⟨∑ i : Option J, theta i, ?_, ?_⟩
  · rw [map_sum]
    calc
      ∑ i : Option J,
          JJMath.Manifold.deRhamDifferential
            (I := SurfaceRealModel) (M := X) (A := ℝ) 1 (theta i) =
          ∑ i : Option J, piece i := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact htheta i
      _ = omega := by
        apply JJMath.Manifold.smoothFormsPointwiseSMul_finset_sum_eq_self_of_sum_eq_one
        intro y
        have hsum := rho.sum_eq_one (show y ∈ (univ : Set X) by simp)
        simpa [finsum_eq_sum_of_fintype] using hsum
  · intro y hyV
    rw [smoothForms_finset_sum_toFun
      SurfaceRealModel theta (Finset.univ : Finset (Option J)) y]
    simp_rw [hthetaSupport _ y hyV]
    simp

/-- A two-form whose support is contained in a compact subset of an exterior
component is globally exact.

%%handwave
name: Exactness of compactly supported mass in an exterior component
statement:
  Let $V$ be an exterior component and let $C\subseteq V$ be compact. Every smooth two-form that vanishes outside $C$ is globally exact.
proof:
  Use the supported primitive theorem for compact mass in $V$ and discard its support conclusion.
-/
theorem IsExteriorComponent.exists_primitive_of_compactSupport
    (E : SmoothRelativelyCompactExhaustion X)
    {K V C : Set X} (hKcompact : IsCompact K)
    (hV : IsExteriorComponent K V)
    (hCcompact : IsCompact C) (hCV : C ⊆ V)
    (omega : JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := X) ℝ 2)
    (hzero : ∀ y : X, y ∉ C → omega.toFun y = 0) :
    ∃ theta : JJMath.Manifold.SmoothForms
        (I := SurfaceRealModel) (M := X) ℝ 1,
      JJMath.Manifold.deRhamDifferential
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1 theta = omega := by
  rcases hV.exists_primitive_of_compactSupport_with_support
      E hKcompact hCcompact hCV omega hzero with
    ⟨theta, htheta, _hsupport⟩
  exact ⟨theta, htheta⟩

end JJMath.Uniformization
